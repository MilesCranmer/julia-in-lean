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

def slotRef (_a : Unit) (i : I) : SlotM α I := fun slots => (.ok i, slots)

def slotUnset (layout : DictLayout) (i : I) : SlotM α Unit :=
  fun slots => (.ok (), updateSlot slots i (unsetCell layout i.val.toNat (slots i)))

def slotRead (i : I) : SlotM α α :=
  fun slots => (match slots i with | some x => .ok x | none => .error .undefinedReference, slots)

def LinearAccessSpec : Prop := ∀ (runtime : DictLayout), ∀ (α β : Type) (n : Nat) (slots : I → Option α)
    (i : I) (x : α) (already : β → Bool) (asTyped : β → α)
    (convert : β → Except Error α) (v : β),
  let inb := 1 ≤ i.val ∧ i.val ≤ (n : Int)
  let converted := if already v then .ok (asTyped v) else convert v
  (unsetindexInt (slotBounds n) slotRef (slotUnset runtime) () i).run slots =
    (if inb then (.ok (), updateSlot slots i (expectedUnset runtime (slots i))) else (.error .bounds, slots)) ∧
  (setindexTyped (slotBounds n) slotRefNew slotStore () x i).run slots =
    (if inb then (.ok (), updateSlot slots i (some x)) else (.error .bounds, slots)) ∧
  (inb → (do
    let _ ← setindexTyped (slotBounds n) slotRefNew slotStore () x i
    slotRead i : SlotM α α).run slots =
      (.ok x, updateSlot slots i (some x))) ∧
  (∀ e, converted = .error e →
    (setindexScalar already asTyped (fun v => slotLift (convert v))
      (setindexTyped (slotBounds n) slotRefNew slotStore) () v i).run slots =
      (.error e, slots)) ∧
  (∀ y, converted = .ok y →
    (setindexScalar already asTyped (fun v => slotLift (convert v))
      (setindexTyped (slotBounds n) slotRefNew slotStore) () v i).run slots =
      (if inb then (.ok (), updateSlot slots i (some y)) else (.error .bounds, slots))) ∧
  (inb → ∀ j, j ≠ i →
    (updateSlot slots i (some x)) j = slots j ∧
    (updateSlot slots i (expectedUnset runtime (slots i))) j = slots j)


def AssignmentSpec : Prop := ∀ (α : Type) (slots : I → Option α) (n : Nat) (i : I),
  (isassignedVector (m := Id) (fun (_ : Unit) j => decide (1 ≤ j.val ∧ j.val ≤ (n : Int)))
    (fun _ j _ => j) (fun j => (slots j).isSome) () i = true ↔
      1 ≤ i.val ∧ i.val ≤ (n : Int) ∧ ∃ x, slots i = some x) ∧
  ∀ (D : Type) (dims : D) (bounds : List I → Bool) (linear : D → List I → I)
      (indices : List I),
    (isassignedArray (m := Id) (fun (_ : Unit) js => bounds js) (fun _ => dims)
      linear (fun _ j _ => j) (fun j => (slots j).isSome) () indices = true ↔
        bounds indices = true ∧ ∃ x, slots (linear dims indices) = some x)

theorem assignmentSpec : AssignmentSpec := by
  intro α slots n i
  constructor
  · by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int)
    · cases hs : slots i <;> simp [isassignedVector, hb, hs, Bind.bind]
    · have hb' : ¬ (1 ≤ i.val ∧ i.val ≤ (n : Int) ∧ ∃ x, slots i = some x) :=
        fun h => hb ⟨h.1, h.2.1⟩
      simp only [isassignedVector, show decide (1 ≤ i.val ∧ i.val ≤ (n : Int)) = false
        from decide_eq_false hb, Bind.bind, Pure.pure, Bool.not_false, ite_true]
      exact ⟨fun h => Bool.noConfusion h, fun h => (hb' h).elim⟩
  · intro D dims bounds linear indices
    cases hb : bounds indices <;> cases hs : slots (linear dims indices) <;>
      simp [isassignedArray, hb, hs, Bind.bind, Pure.pure]

theorem dimension_range_suffix (size : List I → I → Except Error I)
    (hsize : ∀ dims i, size dims i =
      if 1 ≤ i.val then .ok (dims[(i.val - 1).toNat]?.getD one) else .error .bounds)
    (dims : List I) (hd : dims.length < 2 ^ 63) (i : I)
    (hi : 1 ≤ i.val) (he : i.val ≤ (dims.length : Int)) :
    (intRange i (JInt.wrap .i64 dims.length)).mapM (size dims) =
      .ok (dims.drop (i.val - 1).toNat) := by
  have hdim : (JInt.wrap .i64 (dims.length : Int)).val = dims.length := by
    change wrapInt .i64 (dims.length : Int) = dims.length
    apply wrapInt_of_inRange
    simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
    omega
  let offset := (i.val - 1).toNat
  let count := dims.length - offset
  have hcount : ((dims.length : Int) - i.val + 1).toNat = count := by
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
  have hs : ∀ k ∈ List.range count,
      size dims (JInt.wrap .i64 (i.val + (k : Int))) =
        .ok (dims[offset + k]?.getD one) := by
    intro k hk
    have hk' := List.mem_range.mp hk
    rw [hsize, hj k hk', ite_eq_left (by omega)]
    have hidx : (i.val + (k : Int) - 1).toNat = offset + k := by
      dsimp [offset]
      omega
    rw [hidx]
  simp only [Function.comp_def]
  rw [mapM_ok_of_mem _ _ _ hs]
  apply congrArg Except.ok
  apply List.ext_getElem
  · simp [count, offset]
  · intro k hk hk'
    have hlt : offset + k < dims.length := by
      simp only [List.length_map, List.length_range] at hk
      dsimp [count] at hk
      omega
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop,
      List.getElem?_eq_getElem hlt, Option.getD_some]
    rfl

def UnsetIntegerFullSpec : Prop :=
  ∀ (runtime : DictLayout), ∀ (α : Type) (toIndex : Bool → Int → Except Error I) (message : String),
    (∀ b value, toIndex b value =
      if b then .error (.argument message)
      else (JInt.convert (IntTy.i64.name) .i64 value).mapError (fun _ => Error.inexact)) →
    ∀ (n : Nat) (slots : I → Option α) (b : Bool) (value : Int),
      (unsetindexInteger (fun value => slotLift (toIndex b value))
        (unsetindexInt (slotBounds n) slotRef (slotUnset runtime)) () value).run slots =
      if b then (.error (.argument message), slots)
      else
        match (JInt.convert (IntTy.i64.name) .i64 value).mapError (fun _ => Error.inexact) with
        | .error e => (.error e, slots)
        | .ok i =>
          if 1 ≤ i.val ∧ i.val ≤ (n : Int) then (.ok (), updateSlot slots i (expectedUnset runtime (slots i)))
          else (.error .bounds, slots)

def slotGet (n : Nat) (i : I) : SlotM α α := do
  slotBounds n () i
  slotRead i

def ReadableSpec : Prop := ∀ (runtime : DictLayout), ∀ (α : Type) (slots : I → Option α) (n : Nat) (i : I),
  (isassignedVector (m := Id) (fun (_ : Unit) j => decide (1 ≤ j.val ∧ j.val ≤ (n : Int)))
    (fun _ j _ => j) (fun j => (slots j).isSome) () i = true ↔
      ∃ x, (slotGet n i).run slots = (.ok x, slots)) ∧
  (¬ (1 ≤ i.val ∧ i.val ≤ (n : Int)) →
    (slotGet n i).run slots = (.error .bounds, slots)) ∧
  (1 ≤ i.val ∧ i.val ≤ (n : Int) →
    (do
      let _ ← unsetindexInt (slotBounds n) slotRef (slotUnset runtime) () i
      slotRead i : SlotM α α).run slots =
        ((match expectedUnset runtime (slots i) with
          | some value => .ok value
          | none => .error .undefinedReference),
          updateSlot slots i (expectedUnset runtime (slots i))))


def LinearAccessComplete : Prop := LinearAccessSpec ∧ AssignmentSpec ∧ ReadableSpec

def AssignmentLinearArraySpec : Prop := ∀ (α : Type) (slots : I → Option α)
    (dims : List Nat) (bounds : List I → Bool) (linear : List Nat → List I → I),
  (∀ i, bounds [i] = decide (1 ≤ i.val ∧ i.val ≤ (dims.prod : Int))) →
  bounds [] = dims.all (fun d => d == 1) →
  (∀ i, linear dims [i] = i) → linear dims [] = one →
  ∀ i,
    (isassignedArray (m := Id) (fun (_ : Unit) js => bounds js) (fun _ => dims)
      linear (fun _ j _ => j) (fun j => (slots j).isSome) () [i] = true ↔
        1 ≤ i.val ∧ i.val ≤ (dims.prod : Int) ∧ ∃ x, slots i = some x) ∧
    (isassignedArray (m := Id) (fun (_ : Unit) js => bounds js) (fun _ => dims)
      linear (fun _ j _ => j) (fun j => (slots j).isSome) () [] = true ↔
        dims.all (fun d => d == 1) = true ∧ ∃ x, slots one = some x)

def AllLiteralContents : Prop := LiteralContents ∧ ConvertedLiteralContents

theorem allLiteralContents : AllLiteralContents := ⟨literalContents, convertedLiteralContents⟩

def CartesianAssignmentSpec : Prop :=
  ∀ (α β : Type) (slots : I → Option α)
    (bounds : List I → Bool) (linear : List I → Except Error I)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
    (v : β) (i₁ i₂ : I) (rest : List I),
    let indices := i₁ :: i₂ :: rest
    let converted := if already v then .ok (asTyped v) else convert v
    let operation := setindexCartesian (fun x => if already x then some (asTyped x) else none)
      (fun x => slotLift (convert x)) pure
      (setindexCartesianTyped
        (fun _ js => slotLift (if bounds js then .ok () else .error .bounds))
        (fun _ js => slotLift (linear js)) slotRefNew slotStore) () v i₁ i₂ rest
    (∀ e, converted = .error e → operation.run slots = (.error e, slots)) ∧
    (∀ x, converted = .ok x → bounds indices = false →
      operation.run slots = (.error .bounds, slots)) ∧
    (∀ x e, converted = .ok x → bounds indices = true → linear indices = .error e →
      operation.run slots = (.error e, slots)) ∧
    (∀ x i, converted = .ok x → bounds indices = true → linear indices = .ok i →
      operation.run slots = (.ok (), updateSlot slots i (some x)) ∧
      (updateSlot slots i (some x)) i = some x ∧
      ∀ j, j ≠ i → (updateSlot slots i (some x)) j = slots j)

def steppedRangeValues (first step : Int) (n : Nat) : List Int :=
  (List.range n).map (fun k : Nat => first + (k : Int) * step)

abbrev scalarStepRangeGet {T S : IntTy}
    (r : JuliaLean.base.range.StepRange (JInt T) (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false) (fun _ => "")
    (fun r i => ExceptT.lift (JuliaLean.base.range._getindex_AbstractRange r i)) r i

abbrev scalarUnitRangeGet {T S : IntTy}
    (r : JuliaLean.base.range.UnitRange (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false) (fun _ => "")
    (fun r i => ExceptT.lift (JuliaLean.base.range.JGetindex.getindex r i)) r i

abbrev scalarOneToGet {T S : IntTy}
    (r : JuliaLean.base.range.OneTo (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false) (fun _ => "")
    (fun r i => ExceptT.lift (JuliaLean.base.range._getindex_AbstractRange r i)) r i

def ScalarRangeIndexSpec : Prop :=
  (∀ (R α : Type) (get : R → Bool → ExceptT Error JuliaLean.base.range.JlX α) r i,
    (getindexAbstractRange (fun _ : Bool => true) toString get r i).run =
      .ok (.error (.argument ("invalid index: " ++ toString i ++ " of type Bool")))) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.OneTo (JInt T)) (i : JInt S),
    0 ≤ r.stop.val →
    (scalarOneToGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ r.stop.val then
        .ok (.ok (JInt.wrap T i.val))
      else .error (.jl .boundsError)) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.UnitRange (JInt T)) (i : JInt S),
    r.start.val - 1 ≤ r.stop.val →
    (scalarUnitRangeGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ r.stop.val - r.start.val + 1 then
        .ok (.ok (JInt.wrap T (r.start.val + i.val - 1)))
      else .error (.jl .boundsError)) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.StepRange (JInt T) (JInt T))
    (n : Nat) (i : JInt S),
    r.step.val ≠ 0 → r.stop.val = r.start.val + ((n : Int) - 1) * r.step.val →
    (∀ value ∈ steppedRangeValues r.start.val r.step.val n, T.min ≤ value ∧ value ≤ T.max) →
    (scalarStepRangeGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ (n : Int) then
        .ok (.ok (JInt.wrap T (r.start.val + (i.val - 1) * r.step.val)))
      else .error (.jl .boundsError))

def OrdinaryRangeIndexSpec : Prop :=
  ∀ (R α : Type) (values : R → List α)
    (get : R → I → JuliaLean.base.range.JlX α)
    (getBool : R → Bool → ExceptT Error JuliaLean.base.range.JlX α),
    (∀ r i, get r i =
      match (values r)[(i.val - 1).toNat]? with
      | some value => if 1 ≤ i.val then .ok value else .error (.jl .boundsError)
      | none => .error (.jl .boundsError)) →
    ∀ r i,
    ((getindexAbstractRange (m := ExceptT Error JuliaLean.base.range.JlX) (fun _ : I => false)
      (fun _ => "") (fun r i => ExceptT.lift (get r i)) r i).run =
      match (values r)[(i.val - 1).toNat]? with
      | some value =>
        if 1 ≤ i.val then .ok (.ok value) else .error (.jl .boundsError)
      | none => .error (.jl .boundsError)) ∧
    ∀ b, (getindexAbstractRange (fun _ : Bool => true) toString getBool r b).run =
      .ok (.error (.argument ("invalid index: " ++ toString b ++ " of type Bool")))

/-- Cartesian reads neither change memory nor read a cell before the complete
tuple passes the bounds and linear-index checks. -/
def CartesianReadSpec : Prop :=
  ∀ (α : Type) (slots : I → Option α)
    (bounds : List I → Bool) (linear : List I → Except Error I)
    (i₁ i₂ : I) (rest : List I),
    let indices := i₁ :: i₂ :: rest
    let operation := getindexCartesian
      (fun (_ : Unit) js => slotLift (if bounds js then .ok () else .error .bounds))
      (fun _ js => slotLift (linear js)) (fun _ i => slotRead i) () i₁ i₂ rest
    (bounds indices = false → operation.run slots = (.error .bounds, slots)) ∧
    (∀ e, bounds indices = true → linear indices = .error e →
      operation.run slots = (.error e, slots)) ∧
    (∀ i, bounds indices = true → linear indices = .ok i →
      (∀ x, slots i = some x → operation.run slots = (.ok x, slots)) ∧
      (slots i = none → operation.run slots = (.error .undefinedReference, slots)))

def indcopyIndexValues (values : R → List I) : IndcopyTupleIndex R → List I
  | .range r => values r
  | .vector xs => xs

/-- Destination positions and retained source values, independent of indcopy.
The last index collection uses all remaining source dimensions. -/
def indcopyExpected (dims : List I) (indices : List (List I)) :
    List (List I) × List (List I) :=
  let bound := fun axis : Nat =>
    if axis + 1 < indices.length then (dims[axis]?.map Subtype.val).getD 0
    else ((dims.drop axis).map Subtype.val).prod
  let dst := indices.zipIdx |>.map (fun (xs, axis) =>
    xs.zipIdx |>.filterMap (fun (x, k) =>
      if 1 ≤ x.val ∧ x.val ≤ bound axis then some (JInt.wrap .i64 ((k : Int) + 1)) else none))
  let src := indices.zipIdx |>.map (fun (xs, axis) =>
    xs.filter (fun x => decide (1 ≤ x.val ∧ x.val ≤ bound axis)))
  (dst, src)

/-- The range primitives' documented interfaces describe their yielded values,
including the positions of the intersection and valid range slicing. -/
def IndcopyRangeLaws {R : Type} (values : R → List I)
    (find : R → I → I → Jl R) (get : R → R → Jl R) : Prop :=
  (∀ r lo hi, (find r lo hi).map values =
    .ok ((values r).zipIdx |>.filterMap (fun (x, k) =>
      if lo.val ≤ x.val ∧ x.val ≤ hi.val then some (JInt.wrap .i64 ((k : Int) + 1)) else none))) ∧
  (∀ r is, (∀ i ∈ values is, 1 ≤ i.val ∧ i.val ≤ ((values r).length : Int)) →
    (get r is).map values =
      (values is).mapM (indcopyCoreGet (values r)))

/-- Both tuples of ranges and tuples containing integer index vectors accepted
by get! must compute the exact retained positions and source values. -/
def TupleVectorIndcopySpec : Prop :=
  ∀ (R : Type) (values : R → List I) (find : R → I → I → Jl R) (get : R → R → Jl R),
    IndcopyRangeLaws values find get →
    ∀ dims indices,
      0 < indices.length → indices.length ≤ dims.length →
      (∀ n ∈ dims, 0 ≤ n.val) →
      (((dims.map Subtype.val).prod < 2 ^ 63) ∧
        ∀ axis ∈ indices.map (indcopyIndexValues values), axis.length < 2 ^ 63) →
      tupleIndcopy values find get dims indices =
        .ok (indcopyExpected dims (indices.map (indcopyIndexValues values)))
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

theorem vwWindow_get (h : VecAt s handle mem off n slots) (i : Nat) :
    (vwWindow slots off n)[i]? = if i < n.val.toNat then slots[(off.val - 1).toNat + i]? else none := by
  simp only [vwWindow, List.getElem?_take, List.getElem?_drop]

theorem take_prefix_three {A W B : List β} (hA : A.length = a) (hW : W.length = w) :
    (A ++ W ++ B).take (a + w) = A ++ W := by
  subst hA hW
  rw [← List.length_append, List.take_left]
end VectorWindows
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem getindexColon_vector_run {α A : Type} (heap next final : VectorHeap α)
    (a x : A) (n : I) (length : A → VectorM α I)
    (similar : A → I → VectorM α A)
    (copy : A → I → A → I → I → VectorM α Unit)
    (hl : (length a).run heap = .ok (n, heap))
    (ha : (similar a n).run heap = .ok (x, next))
    (hc : 0 < n.val → (copy x one a one n).run next = .ok ((), final))
    (hz : ¬ 0 < n.val → final = next) :
    (getindexColon length similar copy a).run heap = .ok (x, final) := by
  simp only [getindexColon, vector_bind_run, hl, ha]
  split
  · rename_i hp
    simp only [vector_bind_run, hc hp, vector_pure_run]
  · rename_i hp
    simp only [vector_pure_run, hz hp]

def heapColonLength {Tag α : Type} (a : HeapArray Tag) : VectorM α I :=
  pure (JInt.wrap .i64 (a.dimensions.prod : Int))

def heapColonSimilar {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (n : I) :
    VectorM α (HeapArray Tag) :=
  similar418 (fun n => heapAllocateIntDims layout a.elementType [n]) a n

/-- Colon indexing preserves the element type and uses the native vector allocator. -/
abbrev heapColonCopy {Tag α : Type} (layout : Tag → Option MemoryLayout) (src : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  getindexColon heapColonLength (heapColonSimilar layout) heapColonMemoryCopy src
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section HeapRanges

attribute [local irreducible] JInt.wrap wrapInt

theorem unitRangeLength_val (lo hi : I) (h : hi.val < lo.val ∨ (1 ≤ lo.val ∧ hi.val ≤ 4611686018427387904)) :
    (unitRangeLength (lo, hi)).val = max 0 (hi.val - lo.val + 1) := by
  unfold unitRangeLength
  by_cases hlt : hi.val < lo.val
  · rw [if_pos ((jlt_iff hi lo).mpr hlt), ival_zero]
    omega
  · rw [if_neg (fun h' => hlt ((jlt_iff hi lo).mp h'))]
    have hb := ival_bounds lo
    have hb' := ival_bounds hi
    have hs : (hi - lo).val = hi.val - lo.val := ival_sub hi lo (by omega)
    rw [ival_add _ _ (by rw [hs, ival_one]; omega), hs, ival_one]
    omega

/-- `checkbounds(A, lo:hi)` for linear indexing of a heap array (abstractarray.jl:
`checkindex(Bool, inds, r::AbstractRange)`): an empty range is in bounds, otherwise both
endpoints must lie in `1:length(A)`. -/
def heapRangeBounds {Tag α : Type} (a : HeapArray Tag) (r : I × I) : VectorM α Unit := do
  let n ← heapLength a.handle
  if r.1 ≤ r.2 ∧ ¬(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds

theorem heapRangeBounds_run {Tag α : Type} (heap : VectorHeap α) (a : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[a.handle]? = some xs) (hn : xs.length < 2 ^ 62)
    (lo hi : I) :
    (heapRangeBounds a (lo, hi)).run heap =
      if lo.val ≤ hi.val ∧ ¬(1 ≤ lo.val ∧ hi.val ≤ xs.length) then .error .bounds
      else .ok ((), heap) := by
  obtain ⟨hl, hv⟩ := heapLength_of_slots heap a.handle xs hs hn
  simp only [heapRangeBounds, vector_bind_run, hl]
  by_cases hc : lo.val ≤ hi.val ∧ ¬(1 ≤ lo.val ∧ hi.val ≤ xs.length)
  · rw [if_pos hc, if_pos (by simpa only [jle_iff, ival_one, hv] using hc)]
    rfl
  · rw [if_neg hc, if_neg (by simpa only [jle_iff, ival_one, hv] using hc)]
    rfl

/-- `similar(A, axes(lo:hi))`: a fresh vector of the range length and `A`'s element type. -/
def heapRangeSimilar {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (len : I) : VectorM α (HeapArray Tag) :=
  heapAllocateIntDims layout a.elementType [len]

/-- `getindex(A::Array, lo:hi)` (array.jl:981) on the shared heap. -/
abbrev heapRangeGetindex {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (r : I × I) :
    VectorM α (HeapArray Tag) :=
  getindexUnitRange (fun x : I => pure (decide (x.val > 0))) heapRangeBounds
    (fun r => pure (unitRangeLength r)) (fun r => pure (unitRangeLength r))
    (heapRangeSimilar layout)
    (fun _ => pure one) (fun r => pure r.1) heapRangeCopy a r

/-- `A[lo:hi]` (array.jl:981, the "Faster contiguous indexing" method): a range with an endpoint
outside `1:length(A)` raises `BoundsError` unless it is empty; otherwise the result is a fresh
vector of `A`'s element type and the range length holding `A[lo], ..., A[hi]` (unassigned slots
included), and every existing array is untouched. -/
def RangeGetindexSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (lo hi : I),
    heap[src.handle]? = some xs → xs.length < 2 ^ 62 →
    ((lo.val ≤ hi.val ∧ ¬(1 ≤ lo.val ∧ hi.val ≤ xs.length)) →
      (heapRangeGetindex layout src (lo, hi)).run heap = .error .bounds) ∧
    ((hi.val < lo.val ∨ (1 ≤ lo.val ∧ hi.val ≤ xs.length)) →
      ∃ dest next, (heapRangeGetindex layout src (lo, hi)).run heap = .ok (dest, next) ∧
        dest.elementType = src.elementType ∧
        dest.dimensions = [(hi.val - lo.val + 1).toNat] ∧
        next[dest.handle]? = some ((xs.drop (lo.val - 1).toNat).take (hi.val - lo.val + 1).toNat) ∧
        ∀ h, h < heap.length → dest.handle ≠ h ∧ next[h]? = heap[h]?)

def heapShapeCheck {Tag α : Type} (x : HeapArray Tag) (n : I) : VectorM α Unit := do
  let l ← heapLength x.handle
  if l ≠ n then
    throw (.dimensionMismatch ("tried to assign " ++ toString l.val ++ " elements to " ++
      toString n.val ++ " destinations"))

theorem heapShapeCheck_run {Tag α : Type} (heap : VectorHeap α) (x : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[x.handle]? = some xs) (hn : xs.length < 2 ^ 62) (n : I) :
    ((xs.length : Int) ≠ n.val → ∃ message,
      (heapShapeCheck x n).run heap = .error (.dimensionMismatch message)) ∧
    ((xs.length : Int) = n.val → (heapShapeCheck x n).run heap = .ok ((), heap)) := by
  obtain ⟨hl, hv⟩ := heapLength_of_slots heap x.handle xs hs hn
  constructor
  · intro hne
    apply Exists.intro
    simp only [heapShapeCheck, vector_bind_run, hl]
    rw [if_pos (fun h => hne (by rw [← h, hv]))]
    rfl
  · intro heq
    simp only [heapShapeCheck, vector_bind_run, hl]
    rw [if_neg (fun h => h (Subtype.ext (by rw [hv, heq])))]
    rfl

/-- `A[lo:hi] = X` for arrays of one element type (array.jl:1078) on the shared heap. -/
abbrev heapRangeSetindex {Tag α : Type} (a x : HeapArray Tag) (r : I × I) :
    VectorM α (HeapArray Tag) :=
  setindexUnitRange heapRangeBounds unitRangeLength heapShapeCheck Prod.fst heapColonMemoryCopy
    a x r

/-- `A[lo:hi] = X` (array.jl:1078): a non-empty range with an endpoint outside `1:length(A)` raises
`BoundsError`; otherwise a source whose length differs from the range length raises
`DimensionMismatch`; otherwise `A[lo:hi]` becomes the slots of `X` (unassigned ones included),
every other slot of `A` and every other array keeps its slots, and `A` is returned. -/
def RangeSetindexSpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (a x : HeapArray Tag) (ys xs : List (Option α))
    (lo hi : I),
    heap[a.handle]? = some ys → heap[x.handle]? = some xs →
    ys.length < 2 ^ 62 → xs.length < 2 ^ 62 →
    ((lo.val ≤ hi.val ∧ ¬(1 ≤ lo.val ∧ hi.val ≤ ys.length)) →
      (heapRangeSetindex a x (lo, hi)).run heap = .error .bounds) ∧
    ((hi.val < lo.val ∨ (1 ≤ lo.val ∧ hi.val ≤ ys.length)) →
      ((xs.length : Int) ≠ max 0 (hi.val - lo.val + 1) → ∃ message,
        (heapRangeSetindex a x (lo, hi)).run heap = .error (.dimensionMismatch message)) ∧
      ((xs.length : Int) = max 0 (hi.val - lo.val + 1) →
        (heapRangeSetindex a x (lo, hi)).run heap = .ok (a,
          if hi.val < lo.val then heap
          else heap.set a.handle (ys.take (lo.val - 1).toNat ++ xs ++ ys.drop hi.val.toNat))))

theorem rangeSetindexSpec : RangeSetindexSpec := by
  intro Tag α heap a x ys xs lo hi ha hx hyn hxn
  have hyn' : ys.length < 4611686018427387904 := hyn
  have hxn' : xs.length < 4611686018427387904 := hxn
  have hbounds := heapRangeBounds_run heap a ys ha hyn lo hi
  constructor
  · intro hbad
    simp only [heapRangeSetindex, setindexUnitRange, vector_bind_run, hbounds, if_pos hbad]
  · intro hok
    have hnot : ¬(lo.val ≤ hi.val ∧ ¬(1 ≤ lo.val ∧ hi.val ≤ ys.length)) := by
      clear hbounds ha hx; omega
    have hlen := unitRangeLength_val lo hi (by clear hbounds ha hx hnot; omega)
    have hshape := heapShapeCheck_run heap x xs hx hxn (unitRangeLength (lo, hi))
    rw [hlen] at hshape
    constructor
    · intro hne
      obtain ⟨message, hm⟩ := hshape.1 hne
      refine ⟨message, ?_⟩
      simp only [heapRangeSetindex, setindexUnitRange, vector_bind_run, hbounds, if_neg hnot, hm]
    · intro heq
      have hm := hshape.2 heq
      clear hshape
      by_cases hempty : hi.val < lo.val
      · rw [if_pos hempty]
        simp only [heapRangeSetindex, setindexUnitRange, vector_bind_run, hbounds, if_neg hnot, hm]
        rw [if_neg (by rw [hlen]; clear hbounds ha hx hm hok hnot heq; omega)]
        rfl
      · rw [if_neg hempty]
        have hlenv : (unitRangeLength (lo, hi)).val = hi.val - lo.val + 1 := by
          rw [hlen]; clear hbounds ha hx hm hok hnot heq; omega
        have hin : 1 ≤ lo.val ∧ hi.val ≤ ys.length := by
          clear hbounds ha hx hm hlen hlenv heq; omega
        have hxl : (xs.length : Int) = hi.val - lo.val + 1 := by
          clear hbounds ha hx hm hlen hlenv hok hnot; omega
        clear hlen heq hok
        have hcopy := heapUnsafeCopy_run heap a x xs ys hx ha lo one (unitRangeLength (lo, hi))
          (by rw [hlenv]; clear hbounds ha hx hm hnot; omega) hin.1
          (by rw [hlenv]; clear hbounds ha hx hm hnot; omega)
          (by rw [ival_one]; exact Int.le_refl 1)
          (by rw [ival_one, hlenv]; clear hbounds ha hx hm hnot; omega)
        have hx' : (xs.drop (one.val - 1).toNat).take (unitRangeLength (lo, hi)).val.toNat = xs := by
          rw [ival_one, hlenv, show ((1 : Int) - 1).toNat = 0 from rfl, List.drop_zero]
          exact List.take_of_length_le (by clear hbounds ha hx hm hcopy hnot; omega)
        have hd : (lo.val - 1 + (unitRangeLength (lo, hi)).val).toNat = hi.val.toNat := by
          rw [hlenv]; clear hbounds ha hx hm hcopy hx' hnot; omega
        have hpos : (unitRangeLength (lo, hi)).val > 0 := by
          rw [hlenv]; clear hbounds ha hx hm hcopy hx' hd hnot; omega
        rw [hx', hd] at hcopy
        simp only [heapRangeSetindex, setindexUnitRange, vector_bind_run, hbounds, if_neg hnot, hm]
        rw [if_pos hpos]
        simp only [vector_bind_run, hcopy, vector_pure_run]

/-- `A[:] = X` for arrays of one element type (array.jl:1088) on the shared heap. -/
abbrev heapColonSetindex {Tag α : Type} (a x : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  setindexColon (fun a => heapLength a.handle) heapShapeCheck heapColonMemoryCopy a x

/-- `A[:] = X` (array.jl:1088): a source of another length raises `DimensionMismatch`; otherwise
`A` takes the slots of `X` (unassigned ones included), every other array keeps its slots, and `A`
is returned. -/
def ColonSetindexSpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (a x : HeapArray Tag) (ys xs : List (Option α)),
    heap[a.handle]? = some ys → heap[x.handle]? = some xs →
    ys.length < 2 ^ 62 → xs.length < 2 ^ 62 →
    (xs.length ≠ ys.length → ∃ message,
      (heapColonSetindex a x).run heap = .error (.dimensionMismatch message)) ∧
    (xs.length = ys.length → (heapColonSetindex a x).run heap =
      .ok (a, if ys = [] then heap else heap.set a.handle xs))

/-- One run of the `A[:] = X` body whose length check passed and whose copy succeeded. -/
theorem setindexColon_copy_run {Tag α : Type} (length : HeapArray Tag → VectorM α I)
    (shapeCheck : HeapArray Tag → I → VectorM α Unit)
    (copy : HeapArray Tag → I → HeapArray Tag → I → I → VectorM α Unit)
    (a x : HeapArray Tag) (heap heap' : VectorHeap α) (n : I)
    (hl : (length a).run heap = .ok (n, heap)) (hm : (shapeCheck x n).run heap = .ok ((), heap))
    (hpos : n.val > 0) (hcopy : (copy a one x one n).run heap = .ok ((), heap')) :
    (setindexColon length shapeCheck copy a x).run heap = .ok (a, heap') := by
  simp only [setindexColon, vector_bind_run, hl, hm]
  rw [if_pos hpos]
  simp only [vector_bind_run, hcopy, vector_pure_run]

theorem colonSetindexSpec : ColonSetindexSpec := by
  intro Tag α heap a x ys xs ha hx hyn hxn
  have hyn' : ys.length < 4611686018427387904 := hyn
  obtain ⟨hl, hv⟩ := heapLength_of_slots heap a.handle ys ha hyn
  have hshape := heapShapeCheck_run heap x xs hx hxn (JInt.wrap .i64 ys.length)
  rw [hv] at hshape
  constructor
  · intro hne
    obtain ⟨message, hm⟩ := hshape.1 (by exact_mod_cast hne)
    exact ⟨message, by simp only [heapColonSetindex, setindexColon, vector_bind_run, hl, hm]⟩
  · intro heq
    have hm := hshape.2 (by exact_mod_cast heq)
    clear hshape
    by_cases hz : ys = []
    · rw [if_pos hz]
      simp only [heapColonSetindex, setindexColon, vector_bind_run, hl, hm]
      rw [if_neg (by rw [hv, hz]; simp)]
      rfl
    · rw [if_neg hz]
      have hp : 0 < ys.length := List.length_pos_iff.mpr hz
      have hcopy := heapUnsafeCopy_run heap a x xs ys hx ha one one (JInt.wrap .i64 ys.length)
        (by rw [hv]; clear ha hx hl hm; omega) (by rw [ival_one]; exact Int.le_refl 1)
        (by rw [ival_one, hv]; clear ha hx hl hm; omega)
        (by rw [ival_one]; exact Int.le_refl 1) (by rw [ival_one, hv]; clear ha hx hl hm; omega)
      have hw : ys.take (one.val - 1).toNat ++
          (xs.drop (one.val - 1).toNat).take (JInt.wrap .i64 (ys.length : Int)).val.toNat ++
          ys.drop (one.val - 1 + (JInt.wrap .i64 (ys.length : Int)).val).toNat = xs := by
        rw [ival_one, hv, show ((1 : Int) - 1).toNat = 0 from rfl, List.take_zero, List.drop_zero,
          Int.sub_self, Int.zero_add, Int.toNat_natCast, List.drop_length, List.nil_append,
          List.append_nil]
        exact List.take_of_length_le (by clear ha hx hl hm hcopy; omega)
      rw [hw] at hcopy
      have hpos : (JInt.wrap .i64 (ys.length : Int)).val > 0 := by
        rw [hv]; clear ha hx hl hm hcopy; omega
      exact setindexColon_copy_run _ _ _ a x heap _ _ hl hm hpos hcopy


/-- Both same-type assignment methods of array.jl:1078-1096: `A[lo:hi] = X` and `A[:] = X`. -/
def RangeColonSetindexSpec : Prop := RangeSetindexSpec ∧ ColonSetindexSpec

theorem rangeColonSetindexSpec : RangeColonSetindexSpec := ⟨rangeSetindexSpec, colonSetindexSpec⟩
end HeapRanges
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000


def ColonArrayCopySpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (l : MemoryLayout) (heap : VectorHeap α)
    (src : HeapArray Tag) (xs : List (Option α)),
    layout src.elementType = some l →
    heap[src.handle]? = some xs → src.dimensions.prod = xs.length → xs.length < 2 ^ 63 →
    (memoryFits l xs.length →
      ∃ dest next, (heapColonCopy layout src).run heap = .ok (dest, next) ∧
        dest.elementType = src.elementType ∧ dest.dimensions = [xs.length] ∧
        dest.axes = [(1, xs.length)] ∧ next[dest.handle]? = some xs ∧
        (∀ handle, handle < heap.length → dest.handle ≠ handle ∧ next[handle]? = heap[handle]?)) ∧
    (¬ memoryFits l xs.length →
      (heapColonCopy layout src).run heap = .error (.argument genericMemorySizeMessage))
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section VectorSets

variable {α : Type} [DecidableEq α]

theorem setM_id_bind {β γ : Type} (x : Id β) (f : β → Id γ) : x >>= f = f x := rfl

theorem setM_id_map {β γ : Type} (f : β → γ) (x : Id β) : f <$> x = f x := rfl

/-- A `foldlM` over a list whose body only updates the store. -/
theorem setFoldlM_run {β : Type} (F : PUnit → β → SetM α PUnit)
    (step : VecSet α → β → VecSet α)
    (hF : ∀ b st, (F PUnit.unit b).run st = (PUnit.unit, step st b)) :
    ∀ (bs : List β) (st : VecSet α),
      (List.foldlM F PUnit.unit bs).run st = (PUnit.unit, bs.foldl step st) := by
  intro bs
  induction bs with
  | nil => intro st; rfl
  | cons b bs ih =>
    intro st
    simp only [List.foldlM_cons, StateT.run_bind, hF b st, List.foldl_cons]
    exact ih (step st b)
end VectorSets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- The value of `A[i]` for an `Int` index on a heap array with slots `xs`, or `none` when the read
raises. -/

def heapReadable (xs : List (Option α)) (i : I) : Option (Option α) :=
  if 1 ≤ i.val ∧ i.val ≤ (xs.length : Int) then xs[(i.val - 1).toNat]? else none

/-- `A[r]` for a range `r` of `Int` (array.jl:1005, the comprehension `S[ A[i] for i in I ]`) on
the shared heap, with the typed array builder `literal` of the comprehension as a parameter: the
indices are read in the order of `r`; the first index outside `1:length(A)` raises `BoundsError`
and the first unassigned slot `UndefRefError`, before anything is built; otherwise `literal`
receives exactly the values `[A[i] for i in r]`, in order. -/

def RangeIndexGetSpec : Prop :=
  ∀ (Tag α B : Type) (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (literal : List α → VectorM α B) (pre : List I) (vals : List α),
    heap[src.handle]? = some xs →
    pre.map (heapReadable xs) = vals.map (fun v => some (some v)) →
    let run := fun indices : List I => (getindexRange (fun (a : HeapArray Tag) (i : I) =>
      heapGet a.handle i) literal src indices).run heap
    run pre = (literal vals).run heap ∧
    (∀ i post, (i.val < 1 ∨ (xs.length : Int) < i.val) → run (pre ++ i :: post) = .error .bounds) ∧
    (∀ i post, 1 ≤ i.val → i.val ≤ (xs.length : Int) → xs[(i.val - 1).toNat]? = some none →
      run (pre ++ i :: post) = .error .undefinedReference)

def mutableShapeCheck {α : Type} (x : Nat) (n : I) : MutationM α Unit := do
  let l ← mutableLength x
  if l ≠ n then
    throw (.dimensionMismatch ("tried to assign " ++ toString l.val ++ " elements to " ++
      toString n.val ++ " destinations"))

/-- `A[I] = X` (array.jl:1063) for vectors `A` and `X` in mutable memory and an index vector `I`
with `Int` entries `idx`: `checkbounds(A, I)` checks every index, `X` and `I` share no memory
with `A` so `unalias` returns them, `eachindex(X)` is `1:length(X)`, `I[k]` is
`getindex(::Vector, ::Int)`, `X[j]` reads the slot (raising `UndefRefError` when unassigned) and
each store is `setindex!(A::Array{T}, x, i::Int)` (array.jl:1031) with the conversion
`convert(T, x)`. -/

abbrev mutableVectorSetindex {α : Type} (already : α → Bool) (convert : α → Except Error α)
    (a x : Nat) (idx : List I) : MutationM α Nat :=
  setindexVector mutableShapeCheck (fun idx : List I => JInt.wrap .i64 idx.length)
    (fun a idx => idx.forM (fun i => mutableBounds a i)) (fun _ x => pure x)
    (fun _ idx => pure idx) (fun _ => pure one)
    (fun x => do pure (intRange one (← mutableLength x)))
    (fun idx k => stateExceptLift (vectorGet idx k)) mutableGet
    (fun a v i => do
      let _ ← setindexScalar already id (fun v => stateExceptLift (convert v)) mutableTypedSet
        a v i
      pure ())
    a x idx

/-- Reading one slot of the source and converting it; an unassigned slot raises
`UndefRefError`. -/

def storedSlot (already : α → Bool) (convert : α → Except Error α) : Option α → Except Error α
  | some x => storedValue already convert x
  | none => .error .undefinedReference

/-- The slots after the stores `A[i] = v` for the pairs `(i, v)`, in order. -/

def storeAll (ys : List (Option α)) (pairs : List (I × α)) : List (Option α) :=
  pairs.foldl (fun s q => s.set (q.1.val - 1).toNat (some q.2)) ys

/-- The value of the last pair stored at one-based position `p + 1`, if any. -/

def lastStored (pairs : List (I × α)) (p : Nat) : Option α :=
  (pairs.reverse.find? (fun q => decide (q.1.val = (p : Int) + 1))).map Prod.snd

/-- `A[I] = X` for an `Array` `A`, an `AbstractArray` `X` and an `AbstractVector{Int}` `I`
(array.jl:1063; indexed assignment `A[I] = X` in the manual): `DimensionMismatch` unless
`length(X) == length(I)`, then `BoundsError` when an index lies outside `1:length(A)`, both with
nothing changed; otherwise `X[k]`, converted to the element type, is stored at `A[I[k]]` for
`k = 1, 2, ...` in order, so a repeated index keeps its last value, every other slot of `A` keeps
its value, and `X`, the array headers and every other memory are unchanged. An unassigned `X[k]`
raises `UndefRefError` and a failing conversion its error, after `X[1:k-1]` have been stored. -/

def VectorIndexSetSpec : Prop :=
  ∀ (α : Type) (s : MutableMemory α) (a x : Nat) (idx : List I) (already : α → Bool)
    (convert : α → Except Error α),
    s.validVector a → s.validVector x →
    (∀ va vx, s.arrays[a]? = some va → s.arrays[x]? = some vx →
      va.reference.1 ≠ vx.reference.1) →
    idx.length < 2 ^ 62 →
    let ys := s.contents a
    let xs := s.contents x
    let run := (mutableVectorSetindex already convert a x idx).run s
    let others := fun (next : MutableMemory α) => next.arrays = s.arrays ∧
      ∀ mem, (∀ va, s.arrays[a]? = some va → va.reference.1 ≠ mem) →
        next.memories[mem]? = s.memories[mem]?
    ((xs.length : Int) ≠ idx.length →
      ∃ message, run = (.error (.dimensionMismatch message), s)) ∧
    (xs.length = idx.length → (∃ i ∈ idx, ¬(1 ≤ i.val ∧ i.val ≤ (ys.length : Int))) →
      run = (.error .bounds, s)) ∧
    (xs.length = idx.length → (∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ (ys.length : Int)) →
      (∀ k cs e, (xs.take k).mapM (storedSlot already convert) = .ok cs →
        xs[k]?.map (storedSlot already convert) = some (.error e) →
        ∃ next, run = (.error e, next) ∧ others next ∧
          next.contents a = storeAll ys ((idx.take k).zip cs)) ∧
      (∀ cs, xs.mapM (storedSlot already convert) = .ok cs →
        ∃ next, run = (.ok a, next) ∧ others next ∧ next.validVector a ∧
          next.contents a = storeAll ys (idx.zip cs) ∧
          ∀ p, p < ys.length → (next.contents a)[p]? =
            match lastStored (idx.zip cs) p with
            | some v => some (some v)
            | none => ys[p]?))
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

/-- The number of reads and writes in an expression is unchanged by safe indexing. -/
def indexOperations : Expr Atom → Nat
  | .atom _ => 0
  | .node _ args => (args.map indexOperations).sum
  | .ref xs args => indexOperations xs + 1 + (args.map indexOperations).sum
  | .assign lhs rhs => indexOperations lhs + indexOperations rhs
  | .safeGet xs args => indexOperations xs + 1 + (args.map indexOperations).sum
  | .safeSet xs rhs args =>
      indexOperations xs + 1 + indexOperations rhs + (args.map indexOperations).sum
  | .escape body => indexOperations body
termination_by e => sizeOf e

/-- Safe-call constructors are introduced by the rewrite, not by the input AST. -/
def ordinaryExpression : Expr Atom → Prop
  | .atom _ => True
  | .node _ args => ∀ x ∈ args, ordinaryExpression x
  | .ref xs args => ordinaryExpression xs ∧ ∀ x ∈ args, ordinaryExpression x
  | .assign lhs rhs => ordinaryExpression lhs ∧ ordinaryExpression rhs
  | .escape x => ordinaryExpression x
  | .safeGet _ _ | .safeSet _ _ _ => False
termination_by e => sizeOf e

def slotUnset (layout : DictLayout) (i : I) : SlotM α Unit :=
  fun slots => (.ok (), updateSlot slots i (unsetCell layout i.val.toNat (slots i)))

def slotRead (i : I) : SlotM α α :=
  fun slots => (match slots i with | some x => .ok x | none => .error .undefinedReference, slots)

def slotLift (value : Except Error α) : SlotM β α := fun slots => (value, slots)

def slotGet (n : Nat) (i : I) : SlotM α α := do
  slotBounds n () i
  slotRead i

def objectRef {A R D : Type} (a : A) : StateM (A → R × D) R :=
  fun objects => ((objects a).1, objects)

def objectSize {A R D : Type} (a : A) : StateM (A → R × D) D :=
  fun objects => ((objects a).2, objects)

def objectSetRef {A R D : Type} [DecidableEq A] (a : A) (ref : R) : StateM (A → R × D) Unit :=
  fun objects => ((), fun k => if k = a then (ref, (objects k).2) else objects k)

def objectSetSize {A R D : Type} [DecidableEq A] (a : A) (dims : D) : StateM (A → R × D) Unit :=
  fun objects => ((), fun k => if k = a then ((objects k).1, dims) else objects k)

abbrev scalarStepRangeGet {T S : IntTy}
    (r : JuliaLean.base.range.StepRange (JInt T) (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false) (fun _ => "")
    (fun r i => ExceptT.lift (JuliaLean.base.range._getindex_AbstractRange r i)) r i

abbrev scalarUnitRangeGet {T S : IntTy}
    (r : JuliaLean.base.range.UnitRange (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false) (fun _ => "")
    (fun r i => ExceptT.lift (JuliaLean.base.range.JGetindex.getindex r i)) r i

abbrev scalarOneToGet {T S : IntTy}
    (r : JuliaLean.base.range.OneTo (JInt T)) (i : JInt S) :
    ExceptT Error JuliaLean.base.range.JlX (JInt T) :=
  getindexAbstractRange (fun _ => false) (fun _ => "")
    (fun r i => ExceptT.lift (JuliaLean.base.range._getindex_AbstractRange r i)) r i

/-- Tuple entries retain the distinction relevant to Julia dispatch. -/
inductive IndcopyTupleIndex (R : Type) where
  | range (value : R)
  | vector (values : List I)

def indcopyIndexValues (values : R → List I) : IndcopyTupleIndex R → List I
  | .range r => values r
  | .vector xs => xs

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

/-- Destination positions and retained source values, independent of indcopy.
The last index collection uses all remaining source dimensions. -/
def indcopyExpected (dims : List I) (indices : List (List I)) :
    List (List I) × List (List I) :=
  let bound := fun axis : Nat =>
    if axis + 1 < indices.length then (dims[axis]?.map Subtype.val).getD 0
    else ((dims.drop axis).map Subtype.val).prod
  let dst := indices.zipIdx |>.map (fun (xs, axis) =>
    xs.zipIdx |>.filterMap (fun (x, k) =>
      if 1 ≤ x.val ∧ x.val ≤ bound axis then some (JInt.wrap .i64 ((k : Int) + 1)) else none))
  let src := indices.zipIdx |>.map (fun (xs, axis) =>
    xs.filter (fun x => decide (1 ≤ x.val ∧ x.val ≤ bound axis)))
  (dst, src)

/-- `_findin(x, Set(b))` (array.jl:2905, 2898) over `Float64` vectors, with set
membership by `isequal` (set.jl). -/
def setFindinFloat (xs ys : List (JuliaLean.Promotion.Fl JuliaLean.Promotion.double)) :
    MutationM I Nat :=
  findin (fun values => pure values)
    (findinSet (mutableAllocate (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout) 0 zero)
      (fun values => (values.zipIdx 1).map (fun p => (JInt.wrap .i64 (p.2 : Int), p.1)))
      (fun x values => pure (values.any (JuliaLean.C.jlFpiseq x)))
      (mutablePush (MemoryLayoutMetadata.ofRuntime int64RuntimeLayout))) xs ys
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

/-- `checkbounds(A, lo:hi)` for linear indexing of a heap array (abstractarray.jl:
`checkindex(Bool, inds, r::AbstractRange)`): an empty range is in bounds, otherwise both
endpoints must lie in `1:length(A)`. -/
def heapRangeBounds {Tag α : Type} (a : HeapArray Tag) (r : I × I) : VectorM α Unit := do
  let n ← heapLength a.handle
  if r.1 ≤ r.2 ∧ ¬(one ≤ r.1 ∧ r.2 ≤ n) then throw .bounds

/-- `similar(A, axes(lo:hi))`: a fresh vector of the range length and `A`'s element type. -/
def heapRangeSimilar {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (len : I) : VectorM α (HeapArray Tag) :=
  heapAllocateIntDims layout a.elementType [len]

/-- `getindex(A::Array, lo:hi)` (array.jl:981) on the shared heap. -/
abbrev heapRangeGetindex {Tag α : Type} (layout : Tag → Option MemoryLayout) (a : HeapArray Tag) (r : I × I) :
    VectorM α (HeapArray Tag) :=
  getindexUnitRange (fun x : I => pure (decide (x.val > 0))) heapRangeBounds
    (fun r => pure (unitRangeLength r)) (fun r => pure (unitRangeLength r))
    (heapRangeSimilar layout)
    (fun _ => pure one) (fun r => pure r.1) heapRangeCopy a r

/-- `setindex_shape_check(X, n)` (indices.jl: `length(X) == n` or `DimensionMismatch`) for a heap
array `X`. -/
def heapShapeCheck {Tag α : Type} (x : HeapArray Tag) (n : I) : VectorM α Unit := do
  let l ← heapLength x.handle
  if l ≠ n then
    throw (.dimensionMismatch ("tried to assign " ++ toString l.val ++ " elements to " ++
      toString n.val ++ " destinations"))

/-- `A[lo:hi] = X` for arrays of one element type (array.jl:1078) on the shared heap. -/
abbrev heapRangeSetindex {Tag α : Type} (a x : HeapArray Tag) (r : I × I) :
    VectorM α (HeapArray Tag) :=
  setindexUnitRange heapRangeBounds unitRangeLength heapShapeCheck Prod.fst heapColonMemoryCopy
    a x r

/-- `A[:] = X` for arrays of one element type (array.jl:1088) on the shared heap. -/
abbrev heapColonSetindex {Tag α : Type} (a x : HeapArray Tag) : VectorM α (HeapArray Tag) :=
  setindexColon (fun a => heapLength a.handle) heapShapeCheck heapColonMemoryCopy a x
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
section VectorSets

variable {α : Type} [DecidableEq α]
/-- `x ∉ seen` for the tracked set. -/
def setNotin (x : α) (_ : Unit) : SetM α Bool := do
  return !decide (x ∈ (← get).set)

/-- `mapfilter(pred, push!, itr, v)` (abstractset.jl). -/
def mapfilterList (pred : α → SetM α Bool) (push : Unit → α → SetM α Unit) :
    List α → Unit → SetM α Unit
  | [], _ => pure ()
  | x :: xs, v => do
    if ← pred x then push v x
    mapfilterList pred push xs v

/-- The values of `xs` not in `seen`, each once, in order of first appearance. -/
def dedupFrom (seen : List α) : List α → List α
  | [] => []
  | x :: xs => if x ∈ seen then dedupFrom seen xs else x :: dedupFrom (seen ++ [x]) xs

/-- `symdiff!(Set{T}(), v, itrs...)`: the values lying in an odd number of the arguments, each
once, in order of first appearance across `v, itrs...`. -/
def oddSet (v : List α) (itrs : List (List α)) : List α :=
  (dedupFrom [] (v ++ itrs.flatten)).filter
    (fun x => ((v :: itrs).filter (fun l => decide (x ∈ l))).length % 2 == 1)
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

/-- The value `setindex!(A::Array{T}, x, i::Int)` (array.jl:1031) stores: `x` itself when it is
already a `T`, otherwise `convert(T, x)`. -/
def storedValue (already : α → Bool) (convert : α → Except Error α) (x : α) : Except Error α :=
  if already x then .ok x else convert x

/-- Reading one slot of the source and converting it; an unassigned slot raises
`UndefRefError`. -/
def storedSlot (already : α → Bool) (convert : α → Except Error α) : Option α → Except Error α
  | some x => storedValue already convert x
  | none => .error .undefinedReference

/-- The slots after the stores `A[i] = v` for the pairs `(i, v)`, in order. -/
def storeAll (ys : List (Option α)) (pairs : List (I × α)) : List (Option α) :=
  pairs.foldl (fun s q => s.set (q.1.val - 1).toNat (some q.2)) ys

/-- `indcopy(sz, I::Vector)` (array.jl:2965) for `Int` dimensions `dims` and a vector of `Int`
index vectors, with the documented range primitives: `_findin(I[i], 1:b)` lists the positions of
`I[i]` holding values in `1:b`, and `I[i][p]` reads those positions. -/
def vectorIndcopy (find : List I → I → I → Jl (List I)) (get : List I → List I → Jl (List I))
    (dims : List I) (indices : List (List I)) : Jl (List (List I) × List (List I)) :=
  indcopyVector (fun dims : List I => JInt.wrap .i64 (dims.length : Int)) indcopyCoreGet
    (fun indices : List (List I) => JInt.wrap .i64 (indices.length : Int)) indcopyCoreGet
    find get pure dims indices
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

def ScalarRangeIndexSpec : Prop :=
  (∀ (R α : Type) (get : R → Bool → ExceptT Error JuliaLean.base.range.JlX α) r i,
    (getindexAbstractRange (fun _ : Bool => true) toString get r i).run =
      .ok (.error (.argument ("invalid index: " ++ toString i ++ " of type Bool")))) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.OneTo (JInt T)) (i : JInt S),
    0 ≤ r.stop.val →
    (scalarOneToGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ r.stop.val then
        .ok (.ok (JInt.wrap T i.val))
      else .error (.jl .boundsError)) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.UnitRange (JInt T)) (i : JInt S),
    r.start.val - 1 ≤ r.stop.val →
    (scalarUnitRangeGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ r.stop.val - r.start.val + 1 then
        .ok (.ok (JInt.wrap T (r.start.val + i.val - 1)))
      else .error (.jl .boundsError)) ∧
  (∀ (T S : IntTy) (r : JuliaLean.base.range.StepRange (JInt T) (JInt T))
    (n : Nat) (i : JInt S),
    r.step.val ≠ 0 → r.stop.val = r.start.val + ((n : Int) - 1) * r.step.val →
    (∀ value ∈ steppedRangeValues r.start.val r.step.val n, T.min ≤ value ∧ value ≤ T.max) →
    (scalarStepRangeGet r i).run =
      if 1 ≤ i.val ∧ i.val ≤ (n : Int) then
        .ok (.ok (JInt.wrap T (r.start.val + (i.val - 1) * r.step.val)))
      else .error (.jl .boundsError))

/-- `sizehint!(s::Set, n)` (set.jl). -/
def setHint {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (_ : Unit) (n : I) :
    SetVecM K Unit := do
  let s ← setLiftR (JuliaLean.base.set.setSizehint ops n true (← get))
  modify (fun _ => s)

/-- `setCallsKey` for a `Set{T}` whose arguments are already of type `T`. -/
abbrev setCalls (K : Type) (ops : JuliaLean.base.set.DictRuntime K) :
    JuliaLean.base.abstractset.Calls K :=
  setCallsKey K ops (identityKey ops)

/-- Runs an abstractset.jl operation on the `Set` of the state with plain iterables `itrs`, and
stores the resulting `Set`. -/
def setRun {K : Type} (ops : JuliaLean.base.set.DictRuntime K)
    (operation : (setCalls K ops).C → List (setCalls K ops).C →
      Except (setCalls K ops).Error (setCalls K ops).C)
    (itrs : List (List K)) : SetVecM K Unit := do
  let start : Sum (JuliaLean.base.set.SetModel K) (List K) := .inl (← get)
  let r : Except JuliaLean.base.set.Error (Sum (JuliaLean.base.set.SetModel K) (List K)) :=
    operation start (itrs.map (fun xs => (Sum.inr xs : Sum (JuliaLean.base.set.SetModel K) (List K))))
  match ← setLiftR r with
  | .inl s => modify (fun _ => s)
  | .inr _ => throw (Error.assertion "set operation returned a non-Set")

/-- The common hypotheses of the vector set-operation statements: a lawful `Set` runtime for the
element type, and a fully assigned valid store vector `v` holding `xs` with room to grow. -/
def SetVecSetting {K : Type} (ops : JuliaLean.base.set.DictRuntime K) (s : MutableMemory K)
    (v : VectorRef) (xs : List K) (itrs : List (List K)) : Prop :=
  JuliaLean.Proofs.base.set.DictRuntimeLawful ops ∧ s.validVector v.handle ∧
  s.contents v.handle = xs.map some ∧
  ∀ w slots, s.arrays[v.handle]? = some w → s.memories[w.reference.1]? = some slots →
    slots.length + xs.length + itrs.flatten.length + 3 < 2 ^ 62

def oneToCheckIndices : List I → List I → JuliaLean.base.abstractarray.Result Bool
  | inds, [] => JuliaLean.base.abstractarray.checkboundsIndicesNil (fun n : I => .ok n) inds
  | inds, i :: is => JuliaLean.base.abstractarray.checkboundsIndicesCons one
      (fun n i => .ok (JuliaLean.base.abstractarray.checkindexOneTo n i))
      (fun inds' _ => oneToCheckIndices inds' is) inds i is

/-- `_sub2ind_recurse(inds, L, ind, I...)` (abstractarray.jl) with the given `nextL` and
`offsetin` methods and `Int` arithmetic. -/
def sub2indRec (nextL offsetin : I → I → JuliaLean.base.abstractarray.Result I) :
    List I → I → I → List I → JuliaLean.base.abstractarray.Result I
  | inds, stride, ind, [] => .ok (JuliaLean.base.abstractarray.sub2indRecurseDone inds stride ind)
  | [], stride, ind, i :: is => JuliaLean.base.abstractarray.sub2indRecurseEmpty
      (fun i (o : I) => (.ok (i - o) : JuliaLean.base.abstractarray.Result I))
      (fun a b => (.ok (a * b) : JuliaLean.base.abstractarray.Result I))
      (fun a b => (.ok (a + b) : JuliaLean.base.abstractarray.Result I))
      (fun _ stride ind _ => sub2indRec nextL offsetin [] stride ind is) stride ind i is
  | r :: rs, stride, ind, i :: is => JuliaLean.base.abstractarray.sub2indRecurse
      (fun axes : List I => (.ok (axes.headD one) : JuliaLean.base.abstractarray.Result I))
      (fun axes : List I => (.ok axes.tail : JuliaLean.base.abstractarray.Result (List I)))
      nextL offsetin
      (fun a b => (.ok (a * b) : JuliaLean.base.abstractarray.Result I))
      (fun a b => (.ok (a + b) : JuliaLean.base.abstractarray.Result I))
      (fun axes stride ind _ => sub2indRec nextL offsetin axes stride ind is) (r :: rs) stride ind i is

/-- `nextL(L, r::AbstractUnitRange) = L*length(r)` and `offsetin(i, r::AbstractUnitRange) =
i - first(r)` for `OneTo` axes given by their lengths. -/
def oneToSub2ind (axes : List I) (is : List I) : JuliaLean.base.abstractarray.Result I :=
  sub2indRec
    (fun stride r => JuliaLean.base.abstractarray.nextLRange (fun r : I => .ok r)
      (fun a b => (.ok (a * b) : JuliaLean.base.abstractarray.Result I)) stride r)
    (fun i r => JuliaLean.base.abstractarray.offsetinRange (fun _ : I => .ok one)
      (fun i f => (.ok (i - f) : JuliaLean.base.abstractarray.Result I)) i r)
    axes one one is

/-- `nextL(L, l::Integer) = L*l` and `offsetin(i, l::Integer) = i-1` for integer dimensions
(`_sub2ind(dims::DimsInteger, I...)`). -/
def dimsSub2ind (dims : List I) (is : List I) : JuliaLean.base.abstractarray.Result I :=
  sub2indRec
    (fun stride n => JuliaLean.base.abstractarray.nextLInteger
      (fun a b => (.ok (a * b) : JuliaLean.base.abstractarray.Result I)) stride n)
    (fun i n => JuliaLean.base.abstractarray.offsetinInteger
      (fun i o => (.ok (i - o) : JuliaLean.base.abstractarray.Result I)) i n)
    dims one one is

/-- `checkbounds(Bool, A, I...)` (abstractarray.jl) for a heap array: one index is checked
against the linear indices `1:length(A)` (`checkbounds(Bool, A, i)`), any other number of indices
against the axes (`checkbounds_indices`). -/
def heapCheckboundsBool {Tag : Type} (a : HeapArray Tag) (is : List I) :
    JuliaLean.base.abstractarray.Result Bool :=
  match is with
  | [i] => JuliaLean.base.abstractarray.checkboundsOne
      (fun a : HeapArray Tag => .ok (JInt.wrap .i64 (a.dimensions.prod : Int)))
      (fun n i => .ok (JuliaLean.base.abstractarray.checkindexOneTo n i)) a i
  | _ => JuliaLean.base.abstractarray.checkboundsMany
      (fun a : HeapArray Tag => .ok (heapAxes a)) oneToCheckIndices a is

/-- `checkbounds(A, I...)`: `BoundsError` unless `checkbounds(Bool, A, I...)`. -/
def heapCheckbounds {Tag α : Type} (a : HeapArray Tag) (is : List I) : VectorM α Unit :=
  match heapCheckboundsBool a is with
  | .ok true => pure ()
  | _ => throw .bounds

/-- `_to_linear_index(A, I...) = _sub2ind(A, I...)` (abstractarray.jl) for a heap array. -/
def heapToLinear {Tag α : Type} (a : HeapArray Tag) (is : List I) : VectorM α I :=
  match JuliaLean.base.abstractarray.sub2indArray (fun a : HeapArray Tag => .ok (heapAxes a))
      oneToSub2ind a is with
  | .ok k => pure k
  | .error _ => throw .bounds

/-- The documented validity of a Cartesian index with one index per dimension. -/
def cartesianInBounds : List Nat → List I → Bool
  | [], [] => true
  | d :: ds, i :: is => decide (1 ≤ i.val ∧ i.val ≤ (d : Int)) && cartesianInBounds ds is
  | _, _ => false

/-- The zero-based column-major offset of a Cartesian index. -/
def cartesianOffset : List Nat → List I → Int
  | d :: ds, i :: is => (i.val - 1) + (d : Int) * cartesianOffset ds is
  | _, _ => 0

/-- The common hypotheses of the Cartesian statements: a heap array `a` whose slots are `slots`,
with fitting dimensions. -/
def CartesianSetting {Tag α : Type} (heap : VectorHeap α) (a : HeapArray Tag)
    (slots : List (Option α)) : Prop :=
  heap[a.handle]? = some slots ∧ slots.length = a.dimensions.prod ∧
  heapDimensionsFit a.dimensions = true ∧ a.dimensions.prod < 2 ^ 62

/-- `getindex(A::Array, i1::Int, i2::Int, I::Int...)` (array.jl:974; `getindex` docstring in
abstractarray.jl: "Return a subset of array `A` as selected by the indices `inds`") for one index
per dimension, with abstractarray.jl's `checkbounds` and `_to_linear_index`: an index outside
the array raises `BoundsError`; otherwise the element at the column-major position is returned
(`UndefRefError` for an unassigned slot) and the heap is unchanged. -/
def CartesianReadSpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (a : HeapArray Tag) (slots : List (Option α))
    (i₁ i₂ : I) (rest : List I),
    CartesianSetting heap a slots → a.dimensions.length = rest.length + 2 →
    let indices := i₁ :: i₂ :: rest
    let run := (getindexCartesian heapCheckbounds heapToLinear (fun a i => heapGet a.handle i)
      a i₁ i₂ rest).run heap
    (cartesianInBounds a.dimensions indices = false → run = .error .bounds) ∧
    (cartesianInBounds a.dimensions indices = true →
      (∀ x, slots[(cartesianOffset a.dimensions indices).toNat]? = some (some x) →
        run = .ok (x, heap)) ∧
      (slots[(cartesianOffset a.dimensions indices).toNat]? = some none →
        run = .error .undefinedReference))

def CartesianAssignmentSpec : Prop :=
  ∀ (Tag α β : Type) (heap : VectorHeap α) (a : HeapArray Tag) (slots : List (Option α))
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
    (v : β) (i₁ i₂ : I) (rest : List I),
    CartesianSetting heap a slots → a.dimensions.length = rest.length + 2 →
    let indices := i₁ :: i₂ :: rest
    let converted := if already v then .ok (asTyped v) else convert v
    let run := (setindexCartesian (fun x => if already x then some (asTyped x) else none)
      (fun x => liftM (convert x)) pure
      (setindexCartesianTyped heapCheckbounds heapToLinear
        (fun a k _ => pure (a.handle, k)) (fun ref x _ => heapSet ref.1 x ref.2))
      a v i₁ i₂ rest).run heap
    (∀ e, converted = .error e → run = .error e) ∧
    (∀ x, converted = .ok x → cartesianInBounds a.dimensions indices = false →
      run = .error .bounds) ∧
    (∀ x, converted = .ok x → cartesianInBounds a.dimensions indices = true →
      run = .ok (a, heap.set a.handle
        (slots.set (cartesianOffset a.dimensions indices).toNat (some x))))

/-- `isassigned(a::Array, i::Int...)` (array.jl:231; `isassigned` docstring in abstractarray.jl:
"Return `true` if the value at the given index exists in an array, and `false` if it is out of
bounds or has an undefined reference") on a heap array, with `checkbounds(Bool, a, i...)` and
`_sub2ind(size(a), i...)` of abstractarray.jl: one index per dimension gives `true` exactly when it
is in bounds and the slot at its column-major position is assigned; a single linear index gives
`true` exactly when it lies in `1:length(a)` and that slot is assigned; no index gives `true`
exactly when every dimension is one and the only slot is assigned. -/
def AssignmentLinearArraySpec : Prop :=
  ∀ (Tag α : Type) (heap : VectorHeap α) (a : HeapArray Tag) (slots : List (Option α)),
    CartesianSetting heap a slots →
    let assigned := fun (k : Int) => decide (∃ x, slots[k.toNat]? = some (some x))
    let run := fun (is : List I) => (isassignedArray (m := VectorM α)
      (fun a is => match heapCheckboundsBool a is with
        | .ok b => pure b
        | .error _ => throw .bounds)
      (fun a => pure (heapAxes a))
      (fun dims is => match dimsSub2ind dims is with
        | .ok k => pure k
        | .error _ => throw .bounds)
      (fun a k _ => pure (a.handle, k))
      (fun ref => do
        let xs ← heapSlots ref.1
        pure (match xs[(ref.2.val - 1).toNat]? with
          | some (some _) => true
          | _ => false))
      a is).run heap
    (∀ is : List I, is.length = a.dimensions.length → 2 ≤ is.length →
      run is = .ok (cartesianInBounds a.dimensions is &&
        assigned (cartesianOffset a.dimensions is), heap)) ∧
    (∀ i : I, run [i] = .ok (decide (1 ≤ i.val ∧ i.val ≤ (a.dimensions.prod : Int)) &&
        assigned (i.val - 1), heap)) ∧
    (run [] = .ok (a.dimensions.all (fun d => d == 1) && assigned 0, heap))

/-- range.jl's `_findin(r, span)` for `UnitRange{Int}`s. -/
def unitRangeFindin (r : JuliaLean.base.range.UnitRange I) (lo hi : I) :
    Jl (JuliaLean.base.range.UnitRange I) :=
  match JuliaLean.base.range._findin (I := I) r (⟨lo, hi⟩ : JuliaLean.base.range.UnitRange I) with
  | .ok (.inl ρ) => .ok ρ
  | _ => .error .boundsError

/-- range.jl's `getindex(r::AbstractUnitRange, s::AbstractUnitRange{<:Integer})` for
`UnitRange{Int}`s. -/
def unitRangeSlice (r s : JuliaLean.base.range.UnitRange I) : Jl (JuliaLean.base.range.UnitRange I) :=
  match JuliaLean.base.range.getindex_AbstractUnitRange_AbstractUnitRange r s with
  | .ok (.inr u) => .ok u
  | _ => .error .boundsError

/-- The values of a `UnitRange{Int}`. -/
def unitRangeValues (r : JuliaLean.base.range.UnitRange I) : List I := intRange r.start r.stop

/-- `indcopy(sz::Dims, I::Tuple{Vararg{RangeIndex}})` (array.jl:2976), reached through
`get!(X, A, I, default)` (abstractarray.jl), for a tuple of `UnitRange{Int}`s with
`length(I) ≤ length(sz)`, with range.jl's `_findin` and range slicing: the destination entries
are the positions within each range whose values lie in `1:sz[i]` (for the last, in
`1:prod(sz[i:end])`) and the source entries those values, in order. A tuple with an index-vector
entry has no applicable method (`MethodError`). -/
def TupleVectorIndcopySpec : Prop :=
  ∀ (dims : List I) (indices : List (IndcopyTupleIndex (JuliaLean.base.range.UnitRange I))),
    0 < indices.length → indices.length ≤ dims.length →
    (∀ n ∈ dims, 0 ≤ n.val) → (dims.map Subtype.val).prod < 2 ^ 63 →
    (∀ e ∈ indices, ∀ r, e = .range r → 1 ≤ r.start.val ∧ r.start.val ≤ r.stop.val + 1 ∧
      r.stop.val < 2 ^ 62) →
    tupleIndcopy unitRangeValues unitRangeFindin unitRangeSlice dims indices =
      match indices.mapM indcopyRangeEntry with
      | none => .error (.methodError "indcopy")
      | some ranges => .ok (indcopyExpected dims (ranges.map unitRangeValues))

def RangeGetindexOn {Tag α : Type} (layout : Tag → Option MemoryLayout) (el : MemoryLayout)
    (ops : BigIntegerOps) (heap : VectorHeap α)
    (a : HeapArray Tag) (xs : List (Option α)) (f l len : IntegerValue) : Prop :=
  let bounds := fun (a : HeapArray Tag) (_ : Unit) => do
    let n ← heapArrayLength (α := α) a
    let check := JuliaLean.base.abstractarray.checkboundsOne (fun _ => .ok n)
      (JuliaLean.base.abstractarray.checkindexRange (fun (_ : Unit) => .ok (decide (l.val < f.val)))
        (fun _ => .ok f) (fun _ => .ok l)
        (JuliaLean.base.abstractarray.checkindexReal (fun _ : I => .ok one) (fun n : I => .ok n)
          (fun lo (i : IntegerValue) => .ok (decide (lo.val ≤ i.val)))
          (fun (i : IntegerValue) hi => .ok (decide (i.val ≤ hi.val))))) a ()
    match check with
    | .ok true => pure ()
    | _ => throw .bounds
  let run := (getindexUnitRange (m := VectorM α)
    (fun x : IntegerValue => pure (decide (x.val > 0))) bounds (fun _ => pure len)
    (fun _ => pure len)
    (fun (a : HeapArray Tag) (n : IntegerValue) => do
      match n.toInt ops with
      | .ok k => heapVectorAllocate layout a.elementType k
      | .error e => throw e)
    (fun _ => pure one) (fun _ => pure f)
    (fun x xi src si n => do
      let _ ← copyto288 (heapCopyImpl α Tag ops (fun x => .ok x)) x (.ofInt xi) src si n
      pure ()) a ()).run heap
  let window := (xs.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat
  (f.val ≤ l.val → ¬(1 ≤ f.val ∧ l.val ≤ xs.length) → run = .error .bounds) ∧
  ((l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ xs.length)) → memoryFits el window.length →
    ∃ b, run = .ok (b, heap ++ [window]) ∧ b.handle = heap.length ∧
      b.dimensions = [window.length]) ∧
  (1 ≤ f.val → f.val ≤ l.val → l.val ≤ xs.length → ¬ memoryFits el window.length →
    run = .error (.argument genericMemorySizeMessage))

def RangeGetindexSpec : Prop :=
  ∀ (Tag α : Type) (layout : Tag → Option MemoryLayout) (el : MemoryLayout) (ops : BigIntegerOps)
    (heap : VectorHeap α) (a : HeapArray Tag) (xs : List (Option α)),
    layout a.elementType = some el →
    ops.Lawful → heap[a.handle]? = some xs → xs.length < 2 ^ 63 →
    (∀ (t : IntTy) (r : JuliaLean.base.range.UnitRange (JInt t)), r.start.val - 1 ≤ r.stop.val →
      RangeGetindexOn layout el ops heap a xs (.bit t r.start) (.bit t r.stop)
        (match JuliaLean.Proofs.base.range.lengthUnit r with
         | .ok n => .bit _ n
         | .error _ => .bit .i64 zero)) ∧
    (∀ (t : IntTy) (r : JuliaLean.base.range.OneTo (JInt t)), 0 ≤ r.stop.val →
      RangeGetindexOn layout el ops heap a xs (.bit t (JInt.wrap t 1)) (.bit t r.stop)
        (match JuliaLean.Proofs.base.range.lengthOneTo r with
         | .ok n => .bit _ n
         | .error _ => .bit .i64 zero)) ∧
    (∀ f l : IntegerValue, f.isBool = false → l.isBool = false → f.val - 1 ≤ l.val →
      RangeGetindexOn layout el ops heap a xs f l (.big (l.val - f.val + 1)))

def UnsetIntegerFullSpec : Prop :=
  ∀ (runtime : DictLayout), ∀ (α : Type) (ops : BigIntegerOps) (s : MutableMemory α) (a : Nat) (i : IntegerValue),
    ops.Lawful → s.validVector a →
    let xs := s.contents a
    let run := (unsetindexInteger (fun i => stateExceptLift (arrayToIndex ops i))
      (fun a i => do (mutableUnset runtime) a i; pure a) a i).run s
    (i.isBool = true → ∃ message, run = (.error (.argument message), s)) ∧
    (i.isBool = false → ¬ i.fits → run = (.error .inexact, s)) ∧
    (i.isBool = false → i.fits → ¬(1 ≤ i.val ∧ i.val ≤ xs.length) → run = (.error .bounds, s)) ∧
    (i.validIndex xs.length →
      ∃ next, run = (.ok a, next) ∧ next.arrays = s.arrays ∧ next.validVector a ∧
        next.contents a = xs.set (i.val - 1).toNat
          (expectedUnset runtime (xs[(i.val - 1).toNat]?).join) ∧
        (∀ vector slots, s.arrays[a]? = some vector →
          s.memories[vector.reference.1]? = some slots →
          let address := (vector.reference.2.val + i.val - 2).toNat
          next.memories = s.memories.set vector.reference.1
            (slots.set address (expectedUnset runtime (slots[address]?).join))))

def vectorFindinSet (ops : JuliaLean.base.set.DictRuntime I) (xs : List I) (lo hi : I) :
    Jl (List I) :=
  let run := (setFindin ops xs (intRange lo hi)).run (MutableMemory.initial [])
  match run.1 with
  | .ok h => .ok ((run.2.contents h).filterMap id)
  | .error _ => .error (.argumentError "Set operation failed")

/-- `indcopy(sz::Dims, I::Vector)` (array.jl:2965, under "Copying subregions") for a vector of
`Int` index vectors with `length(I) ≤ length(sz)`: for each `i`, the destination entry lists the
positions within `I[i]` whose values lie in `1:sz[i]` (for the last `i`, in `1:prod(sz[i:end])`)
and the source entry lists those values, in order. `_findin` is this file's, with set.jl's
`Set(1:b)` for any lawful `Int` `Set` runtime, and `I[i][p]` the checked vector read. -/
def VectorIndcopySpec : Prop :=
  ∀ (ops : JuliaLean.base.set.DictRuntime I) (dims : List I) (indices : List (List I)),
    JuliaLean.Proofs.base.set.DictRuntimeLawful ops →
    ops.equal = JuliaLean.base.operators.isequalDefault JuliaLean.base.int.eq →
    0 < indices.length → indices.length ≤ dims.length →
    (∀ n ∈ dims, 0 ≤ n.val) →
    (dims.map Subtype.val).prod < 2 ^ 62 → (∀ axis ∈ indices, axis.length < 2 ^ 62) →
    vectorIndcopy (vectorFindinSet ops) (fun xs ps => ps.mapM (indcopyCoreGet xs)) dims indices =
      .ok (indcopyExpected dims indices)
end round4
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
section IndexGets

theorem heapGet_of_readable {α : Type} (heap : VectorHeap α) (handle : Nat)
    (xs : List (Option α)) (hs : heap[handle]? = some xs) (i : I) (v : α)
    (h : heapReadable xs i = some (some v)) :
    (heapGet handle i).run heap = .ok (v, heap) := by
  rw [heapGet_run heap handle xs hs i]
  unfold heapReadable at h
  by_cases hc : 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)
  · rw [if_pos hc] at h
    rw [if_pos hc, h]
  · rw [if_neg hc] at h
    cases h

theorem heapGet_mapM_ok {α : Type} (heap : VectorHeap α) (handle : Nat) (xs : List (Option α))
    (hs : heap[handle]? = some xs) :
    ∀ (pre : List I) (vals : List α),
      pre.map (heapReadable xs) = vals.map (fun v => some (some v)) →
      (pre.mapM (fun i => heapGet handle i)).run heap = .ok (vals, heap)
  | [], vals, h => by
    cases vals with
    | nil => rfl
    | cons v vs => simp at h
  | i :: is, vals, h => by
    cases vals with
    | nil => simp at h
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hg := heapGet_of_readable heap handle xs hs i v h.1
      have ih := heapGet_mapM_ok heap handle xs hs is vs h.2
      simp only [List.mapM_cons, vector_bind_run, hg, ih, vector_pure_run]

theorem heapGet_mapM_error {α : Type} (heap : VectorHeap α) (handle : Nat) (xs : List (Option α))
    (hs : heap[handle]? = some xs) (i : I) (post : List I) (e : Error)
    (hi : (heapGet handle i).run heap = .error e) :
    ∀ (pre : List I) (vals : List α),
      pre.map (heapReadable xs) = vals.map (fun v => some (some v)) →
      ((pre ++ i :: post).mapM (fun i => heapGet handle i)).run heap = .error e
  | [], _, _ => by
    simp only [List.nil_append, List.mapM_cons, vector_bind_run, hi]
  | j :: js, vals, h => by
    cases vals with
    | nil => simp at h
    | cons v vs =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hg := heapGet_of_readable heap handle xs hs j v h.1
      have ih := heapGet_mapM_error heap handle xs hs i post e hi js vs h.2
      simp only [List.cons_append, List.mapM_cons, vector_bind_run, hg, ih]

theorem rangeIndexGetSpec : RangeIndexGetSpec := by
  intro Tag α B heap src xs literal pre vals hs hpre
  simp only
  refine ⟨?_, fun i post hbad => ?_, fun i post hi1 hin hun => ?_⟩
  · simp only [getindexRange, vector_bind_run,
      heapGet_mapM_ok heap src.handle xs hs pre vals hpre]
  · have hi : (heapGet src.handle i).run heap = .error .bounds := by
      rw [heapGet_run heap src.handle xs hs i, if_neg (by omega)]
    simp only [getindexRange, vector_bind_run,
      heapGet_mapM_error heap src.handle xs hs i post _ hi pre vals hpre]
  · have hi : (heapGet src.handle i).run heap = .error .undefinedReference := by
      rw [heapGet_run heap src.handle xs hs i, if_pos ⟨hi1, hin⟩, hun]
    simp only [getindexRange, vector_bind_run,
      heapGet_mapM_error heap src.handle xs hs i post _ hi pre vals hpre]
end IndexGets
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace round4
open JuliaLean JuliaLean.base.array
section CartesianReadProof

local notation "M64" => ((2 ^ IntTy.i64.bits : Nat) : Int)

/-- The column-major offset over `Int` dimensions, as `_sub2ind` computes it. -/
private def cartesianOffsetInt : List I → List I → Int
  | d :: ds, i :: is => (i.val - 1) + d.val * cartesianOffsetInt ds is
  | _, _ => 0

private theorem emod64_add_congr {a a' b b' : Int} (ha : a % M64 = a' % M64)
    (hb : b % M64 = b' % M64) : (a + b) % M64 = (a' + b') % M64 := by
  rw [Int.add_emod, ha, hb, ← Int.add_emod]

private theorem emod64_mul_congr {a a' b b' : Int} (ha : a % M64 = a' % M64)
    (hb : b % M64 = b' % M64) : (a * b) % M64 = (a' * b') % M64 := by
  rw [Int.mul_emod, ha, hb, ← Int.mul_emod]

private theorem i64_add_emod (a b : I) : (a + b).val % M64 = (a.val + b.val) % M64 :=
  JuliaLean.Proofs.base.int.wrapInt_emod_self .i64 (a.val + b.val)

private theorem i64_sub_emod (a b : I) : (a - b).val % M64 = (a.val - b.val) % M64 :=
  JuliaLean.Proofs.base.int.wrapInt_emod_self .i64 (a.val - b.val)

private theorem i64_mul_emod (a b : I) : (a * b).val % M64 = (a.val * b.val) % M64 :=
  JuliaLean.Proofs.base.int.wrapInt_emod_self .i64 (a.val * b.val)

private theorem one_val_eq : one.val = 1 := rfl

private theorem sub2indRec_cartesianOffset
    (nextL offsetin : I → I → JuliaLean.base.abstractarray.Result I)
    (hnext : ∀ stride d, nextL stride d = .ok (stride * d))
    (hoff : ∀ i d, offsetin i d = .ok (i - one))
    (dims indices : List I) (stride ind : I)
    (hrank : dims.length = indices.length) :
    sub2indRec nextL offsetin dims stride ind indices =
      .ok (JInt.wrap .i64
        (ind.val + stride.val * cartesianOffsetInt dims indices)) := by
  induction dims generalizing indices stride ind with
  | nil =>
      cases indices with
      | nil =>
          change (Except.ok ind : JuliaLean.base.abstractarray.Result I) =
            .ok (JInt.wrap .i64 (ind.val + stride.val * cartesianOffsetInt [] []))
          simp only [cartesianOffsetInt, Int.mul_zero, Int.add_zero]
          apply congrArg Except.ok
          apply Subtype.ext
          change ind.val = wrapInt .i64 ind.val
          exact (JuliaLean.Proofs.base.int.wrapInt_val ind).symm
      | cons i is => simp at hrank
  | cons d ds ih =>
      cases indices with
      | nil => simp at hrank
      | cons i is =>
          have hrank' : ds.length = is.length := by simp at hrank; omega
          let stride' := stride * d
          let ind' := ind + (i - one) * stride
          have hstep :
              sub2indRec nextL offsetin (d :: ds) stride ind (i :: is) =
                sub2indRec nextL offsetin ds stride' ind' is := by
            simp [sub2indRec, JuliaLean.base.abstractarray.sub2indRecurse,
              hnext, hoff, stride', ind', Bind.bind, Pure.pure,
              Except.bind, Except.pure]
          rw [hstep, ih is stride' ind' hrank']
          apply congrArg Except.ok
          apply Subtype.ext
          show wrapInt .i64 (ind'.val + stride'.val * cartesianOffsetInt ds is) =
            wrapInt .i64 (ind.val + stride.val * (i.val - 1 + d.val * cartesianOffsetInt ds is))
          apply JuliaLean.Proofs.base.int.wrapInt_congr
          have hcalc :
              ind.val + (i.val - 1) * stride.val +
                  (stride.val * d.val) * cartesianOffsetInt ds is =
                ind.val + stride.val *
                  ((i.val - 1) + d.val * cartesianOffsetInt ds is) := by
            calc
              _ = ind.val + (i.val - 1) * stride.val +
                    stride.val * (d.val * cartesianOffsetInt ds is) := by
                    rw [Int.mul_assoc]
              _ = ind.val + stride.val * (i.val - 1) +
                    stride.val * (d.val * cartesianOffsetInt ds is) := by
                    rw [Int.mul_comm (i.val - 1) stride.val]
              _ = ind.val + (stride.val * (i.val - 1) +
                    stride.val * (d.val * cartesianOffsetInt ds is)) := by
                    rw [Int.add_assoc]
              _ = ind.val + stride.val *
                    ((i.val - 1) + d.val * cartesianOffsetInt ds is) := by
                    rw [← Int.mul_add]
          have hsubOne : (i - one).val % M64 = (i.val - 1) % M64 := by
            rw [i64_sub_emod, one_val_eq]
          have hprodIdx : ((i - one) * stride).val % M64 = ((i.val - 1) * stride.val) % M64 := by
            rw [i64_mul_emod]
            exact emod64_mul_congr hsubOne rfl
          have e1 : ind'.val % M64 = (ind.val + (i.val - 1) * stride.val) % M64 := by
            show (ind + (i - one) * stride).val % M64 = _
            rw [i64_add_emod]
            exact emod64_add_congr rfl hprodIdx
          have e2 : stride'.val % M64 = (stride.val * d.val) % M64 := i64_mul_emod stride d
          have e3 := emod64_add_congr e1
            (emod64_mul_congr e2 (rfl : cartesianOffsetInt ds is % M64 = _))
          exact e3.trans (congrArg (· % M64) hcalc)

private theorem cartesianOffsetInt_heapAxes (dims : List Nat) (indices : List I)
    (hfit : heapDimensionsFit dims = true) (hrank : dims.length = indices.length) :
    cartesianOffsetInt (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))) indices =
      cartesianOffset dims indices := by
  induction dims generalizing indices with
  | nil =>
      cases indices with
      | nil => rfl
      | cons i is => simp at hrank
  | cons d ds ih =>
      cases indices with
      | nil => simp at hrank
      | cons i is =>
          have hfitParts : d < 2 ^ 63 ∧ heapDimensionsFit ds = true := by
            simpa [heapDimensionsFit] using hfit
          have hrank' : ds.length = is.length := by simp at hrank; omega
          have hd := heapNatDimension_value (d :: ds) hfit d (by simp)
          simp only [List.map_cons, cartesianOffsetInt, cartesianOffset]
          rw [hd, ih is hfitParts.2 hrank']

private theorem cartesianOffset_bounds (dims : List Nat) (indices : List I)
    (hrank : dims.length = indices.length)
    (hbound : cartesianInBounds dims indices = true) :
    0 ≤ cartesianOffset dims indices ∧ cartesianOffset dims indices < dims.prod := by
  induction dims generalizing indices with
  | nil =>
      cases indices with
      | nil => simp [cartesianOffset]
      | cons i is => simp at hrank
  | cons d ds ih =>
      cases indices with
      | nil => simp at hrank
      | cons i is =>
          have hrank' : ds.length = is.length := by simp at hrank; omega
          have hparts : (1 ≤ i.val ∧ i.val ≤ (d : Int)) ∧
              cartesianInBounds ds is = true := by
            simpa [cartesianInBounds, Bool.and_eq_true, decide_eq_true_eq] using hbound
          obtain ⟨ht0, htt⟩ := ih is hrank' hparts.2
          have hhead : 0 ≤ i.val - 1 ∧ i.val - 1 < (d : Int) := by omega
          have htaille : cartesianOffset ds is + 1 ≤ ds.prod := by omega
          have hprod : ((d :: ds).prod : Int) = (d : Int) * ds.prod := by simp
          constructor
          · show 0 ≤ (i.val - 1) + (d : Int) * cartesianOffset ds is
            have hm := Int.mul_nonneg (show (0 : Int) ≤ d by omega) ht0
            omega
          · show (i.val - 1) + (d : Int) * cartesianOffset ds is < (((d :: ds).prod : Nat) : Int)
            rw [hprod]
            have h1 : (d : Int) * (cartesianOffset ds is + 1) ≤ (d : Int) * ds.prod :=
              Int.mul_le_mul_of_nonneg_left htaille (by omega)
            rw [Int.mul_add, Int.mul_one] at h1
            omega

private theorem heapToLinear_cartesian {Tag α : Type}
    (heap : VectorHeap α) (a : HeapArray Tag) (indices : List I)
    (hfit : heapDimensionsFit a.dimensions = true)
    (hrank : a.dimensions.length = indices.length) :
    (heapToLinear a indices).run heap =
      .ok (JInt.wrap .i64 (cartesianOffset a.dimensions indices + 1), heap) := by
  have hsub : oneToSub2ind (heapAxes a) indices =
      .ok (JInt.wrap .i64 (cartesianOffset a.dimensions indices + 1)) := by
    have h := sub2indRec_cartesianOffset
      (fun stride r => JuliaLean.base.abstractarray.nextLRange (fun r : I => .ok r)
        (fun a b => (.ok (a * b) : JuliaLean.base.abstractarray.Result I)) stride r)
      (fun i r => JuliaLean.base.abstractarray.offsetinRange (fun _ : I => .ok one)
        (fun i f => (.ok (i - f) : JuliaLean.base.abstractarray.Result I)) i r)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (a.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int))) indices one one
      (by simp [hrank])
    rw [cartesianOffsetInt_heapAxes a.dimensions indices hfit hrank, one_val_eq,
      Int.one_mul, Int.add_comm 1] at h
    exact h
  simpa [heapToLinear, JuliaLean.base.abstractarray.sub2indArray, hsub,
    StateT.run, StateT.pure, Bind.bind, Pure.pure, Except.bind, Except.pure]

private theorem checkindexOneTo_i64_bounds (last index : JInt .i64)
    (hnonneg : 0 ≤ last.val) :
    JuliaLean.base.abstractarray.checkindexOneTo last index = true ↔
      1 ≤ index.val ∧ index.val ≤ last.val := by
  have indexRange := index.property
  have lastRange := last.property
  change
    (decide (wrapInt IntTy.i64.toUnsigned
      (wrapInt IntTy.i64 (index.val - wrapInt IntTy.i64 1)) <
      wrapInt IntTy.i64.toUnsigned last.val) = true ↔ _)
  simp only [decide_eq_true_eq]
  simp [wrapInt, IntTy.toUnsigned, IntTy.min, IntTy.max,
    IntTy.signed, IntTy.bits] at indexRange lastRange ⊢
  omega

private theorem oneToCheckIndices_cons_true (inds : List I) (i : I) (is : List I)
    (h : JuliaLean.base.abstractarray.checkindexOneTo (inds.headD one) i = true) :
    oneToCheckIndices inds (i :: is) = oneToCheckIndices inds.tail is := by
  simp only [oneToCheckIndices, JuliaLean.base.abstractarray.checkboundsIndicesCons, h]
  rfl

private theorem oneToCheckIndices_cons_false (inds : List I) (i : I) (is : List I)
    (h : JuliaLean.base.abstractarray.checkindexOneTo (inds.headD one) i = false) :
    oneToCheckIndices inds (i :: is) = .ok false := by
  simp only [oneToCheckIndices, JuliaLean.base.abstractarray.checkboundsIndicesCons, h]
  rfl

private theorem oneToCheckIndices_cartesian (dims : List Nat) (indices : List I)
    (hfit : heapDimensionsFit dims = true) (hrank : dims.length = indices.length) :
    oneToCheckIndices (dims.map (fun n : Nat => JInt.wrap .i64 (n : Int))) indices =
      .ok (cartesianInBounds dims indices) := by
  induction dims generalizing indices with
  | nil =>
    cases indices with
    | nil =>
      simp [oneToCheckIndices, cartesianInBounds,
        JuliaLean.base.abstractarray.checkboundsIndicesNil,
        JuliaLean.base.abstractarray.allTupleM, pure, Except.pure]
    | cons i is => simp at hrank
  | cons d ds ih =>
    cases indices with
    | nil => simp at hrank
    | cons i is =>
      have hfit' : d < 2 ^ 63 ∧ heapDimensionsFit ds = true := by
        simpa [heapDimensionsFit] using hfit
      have hlast := heapNatDimension_value (d :: ds) hfit d (by simp)
      have hnonneg : 0 ≤ (JInt.wrap .i64 (d : Int)).val := by
        rw [hlast]
        omega
      have hcheck := checkindexOneTo_i64_bounds
        (JInt.wrap .i64 (d : Int)) i hnonneg
      rw [hlast] at hcheck
      have htail : ds.length = is.length := by simp at hrank; omega
      have hrec := ih is hfit'.2 htail
      by_cases hb : 1 ≤ i.val ∧ i.val ≤ (d : Int)
      · have htrue := hcheck.mpr hb
        rw [List.map_cons, oneToCheckIndices_cons_true _ _ _ (by simpa using htrue),
          List.tail_cons, hrec]
        simp only [cartesianInBounds, decide_eq_true hb, Bool.true_and]
      · have hfalse :
            JuliaLean.base.abstractarray.checkindexOneTo
              (JInt.wrap .i64 (d : Int)) i = false := by
          cases hv : JuliaLean.base.abstractarray.checkindexOneTo
            (JInt.wrap .i64 (d : Int)) i
          · rfl
          · exact False.elim (hb (hcheck.mp hv))
        rw [List.map_cons, oneToCheckIndices_cons_false _ _ _ (by simpa using hfalse)]
        simp only [cartesianInBounds, decide_eq_false hb, Bool.false_and]

set_option maxRecDepth 32768 in
private theorem heapCheckboundsBool_cartesian {Tag : Type}
    (a : HeapArray Tag) (i₁ i₂ : I) (rest : List I)
    (hfit : heapDimensionsFit a.dimensions = true)
    (hrank : a.dimensions.length = rest.length + 2) :
    heapCheckboundsBool a (i₁ :: i₂ :: rest) =
      .ok (cartesianInBounds a.dimensions (i₁ :: i₂ :: rest)) := by
  have hindices : a.dimensions.length = (i₁ :: i₂ :: rest).length := by
    rw [hrank]
    simp
  change oneToCheckIndices
    (a.dimensions.map (fun n : Nat => JInt.wrap .i64 (n : Int)))
    (i₁ :: i₂ :: rest) = .ok (cartesianInBounds a.dimensions (i₁ :: i₂ :: rest))
  exact oneToCheckIndices_cartesian a.dimensions (i₁ :: i₂ :: rest) hfit hindices

set_option maxRecDepth 32768 in
theorem cartesianReadSpec_proven : CartesianReadSpec := by
  intro Tag α heap a slots i₁ i₂ rest hsetting hrank
  change (cartesianInBounds a.dimensions (i₁ :: i₂ :: rest) = false →
      (getindexCartesian heapCheckbounds heapToLinear
        (fun a i => heapGet a.handle i) a i₁ i₂ rest).run heap = .error .bounds) ∧
    (cartesianInBounds a.dimensions (i₁ :: i₂ :: rest) = true →
      (∀ x, slots[(cartesianOffset a.dimensions (i₁ :: i₂ :: rest)).toNat]? =
        some (some x) →
        (getindexCartesian heapCheckbounds heapToLinear
          (fun a i => heapGet a.handle i) a i₁ i₂ rest).run heap = .ok (x, heap)) ∧
      (slots[(cartesianOffset a.dimensions (i₁ :: i₂ :: rest)).toNat]? = some none →
        (getindexCartesian heapCheckbounds heapToLinear
          (fun a i => heapGet a.handle i) a i₁ i₂ rest).run heap =
            .error .undefinedReference))
  rcases hsetting with ⟨hslots, hlen, hfit, hprod⟩
  have hrank' : a.dimensions.length = (i₁ :: i₂ :: rest).length := by
    simp
    omega
  constructor
  · intro hout
    have hcb : (heapCheckbounds a (i₁ :: i₂ :: rest) : VectorM α Unit) = throw .bounds := by
      unfold heapCheckbounds
      rw [heapCheckboundsBool_cartesian a i₁ i₂ rest hfit hrank, hout]
      all_goals rfl
    simp only [getindexCartesian, hcb, vector_bind_run, vector_throw_run]
  · intro hbound
    have hcb : (heapCheckbounds a (i₁ :: i₂ :: rest) : VectorM α Unit) = pure () := by
      unfold heapCheckbounds
      rw [heapCheckboundsBool_cartesian a i₁ i₂ rest hfit hrank, hbound]
      all_goals rfl
    have hoff := cartesianOffset_bounds a.dimensions (i₁ :: i₂ :: rest) hrank' hbound
    have hlinear := heapToLinear_cartesian heap a (i₁ :: i₂ :: rest) hfit hrank'
    have hmain : (getindexCartesian heapCheckbounds heapToLinear
        (fun a i => heapGet a.handle i) a i₁ i₂ rest).run heap =
        (heapGet a.handle
          (JInt.wrap .i64 (cartesianOffset a.dimensions (i₁ :: i₂ :: rest) + 1))).run heap := by
      simp only [getindexCartesian, hcb, vector_bind_run, vector_pure_run, hlinear]
    rw [hmain]
    generalize cartesianOffset a.dimensions (i₁ :: i₂ :: rest) = offset at hoff ⊢
    have hprodInt : (a.dimensions.prod : Int) < 2 ^ 62 := by exact_mod_cast hprod
    have hlenInt : (slots.length : Int) = a.dimensions.prod := by exact_mod_cast hlen
    have hindexVal : (JInt.wrap .i64 (offset + 1)).val = offset + 1 := by
      change wrapInt .i64 (offset + 1) = offset + 1
      apply wrapInt_of_inRange
      constructor
      · simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
        omega
      · simp [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits]
        omega
    have hbounds : 1 ≤ offset + 1 ∧ offset + 1 ≤ (slots.length : Int) := by omega
    have hgetrun := heapGet_run heap a.handle slots hslots (JInt.wrap .i64 (offset + 1))
    rw [hindexVal, if_pos hbounds, Int.add_sub_cancel] at hgetrun
    rw [hgetrun]
    constructor
    · intro x hslot
      rw [hslot]
      all_goals rfl
    · intro hslot
      rw [hslot]
      all_goals rfl
end CartesianReadProof
end round4
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

private theorem nextIntIndex_max :
    nextIntIndex (JInt.wrap .i64 9223372036854775807) =
      .ok (JInt.wrap .i64 (-9223372036854775808)) := by
  decide
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
open JuliaLean.base.range (OneTo UnitRange)
open JuliaLean.Proofs.base.array.round6dcollect3
section
variable {E U α β St : Type}


theorem liftRange_ok {γ : Type} (x : γ) :
    (liftRange (.ok x : JuliaLean.base.range.JlX γ) : M E U α γ) = pure x := rfl
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
open JuliaLean JuliaLean.base.array
section
set_option maxHeartbeats 1000000
attribute [local irreducible] JInt.wrap wrapInt

theorem colonSimilar_run {Tag α : Type} (layout : Tag → Option MemoryLayout) (l : MemoryLayout)
    (heap : VectorHeap α) (src : HeapArray Tag) (xs : List (Option α))
    (hl : layout src.elementType = some l) (hn : xs.length < 2 ^ 63) :
    (heapColonSimilar layout src (JInt.wrap .i64 xs.length)).run heap =
      if memoryFits l xs.length then
        .ok (⟨heap.length, src.elementType, [xs.length], [(1, xs.length)]⟩,
          heap ++ [List.replicate xs.length none])
      else .error (.argument genericMemorySizeMessage) := by
  unfold heapColonSimilar similar418 heapAllocateIntDims
  rw [opusGrowth.heapArrayUndef_run layout src.elementType l hl]
  have hv := collectorLengthFits xs.length hn
  simp only [List.map_cons, List.map_nil, hv]
  unfold allocOutcome arrayAllocError
  simp only [Int.not_lt.mpr (Int.natCast_nonneg xs.length), Int.toNat_natCast,
    false_or, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.mul_one]
  split <;> simp_all

theorem colonArrayCopySpec : ColonArrayCopySpec := by
  intro Tag α layout l heap src xs hlayout hslots hprod hsmall
  have hv := collectorLengthFits xs.length hsmall
  have hlen : (heapColonLength src : VectorM α I).run heap =
      .ok (JInt.wrap .i64 xs.length, heap) := by
    simp only [heapColonLength, hprod, vector_pure_run]
  have ha := colonSimilar_run layout l heap src xs hlayout hsmall
  constructor
  · intro hfit
    rw [if_pos hfit] at ha
    let dest : HeapArray Tag := ⟨heap.length,src.elementType,[xs.length],[(1,xs.length)]⟩
    let allocated : VectorHeap α := heap ++ [List.replicate xs.length none]
    have hslt : src.handle < heap.length := (List.getElem?_eq_some_iff.mp hslots).choose
    have hsrc : allocated[src.handle]? = some xs := by
      simpa [allocated, List.getElem?_append_left hslt] using hslots
    have hdest : allocated[heap.length]? = some (List.replicate xs.length none) := by simp [allocated]
    have hm : ∀ ys : List (Option α), ys.mapM (fun x => Except.ok (ε := Error) x) = .ok ys := by
      intro ys
      induction ys with
      | nil => rfl
      | cons x ys ih => simp [List.mapM_cons, ih, Bind.bind, Pure.pure, Except.bind, Except.pure]
    have hc : (heapColonMemoryCopy dest one src one (JInt.wrap .i64 xs.length)).run allocated =
        .ok ((), heap ++ [xs]) := by
      by_cases hz : xs.length = 0
      · have hv0 : (JInt.wrap .i64 xs.length).val = 0 := by rw [hv,hz]; rfl
        rw [heapUnsafeCopy_zero_run allocated dest src one one _ hv0]
        have hx : xs = [] := List.length_eq_zero_iff.mp hz
        simp [allocated,hx]
      · unfold heapColonMemoryCopy
        apply unsafeCopyArray_vector_run
        · rw [hv]; omega
        · rw [heapCopyReferences_whole_run (fun x => Except.ok (ε := Error) x)
            allocated heap.length src.handle xs (List.replicate xs.length none)
            hsrc hdest (by simp) hsmall, hm xs]
          simp [Except.map, allocated, List.set_append_right]
    refine ⟨dest, heap ++ [xs], ?_, rfl, rfl, rfl, by simp [dest], ?_⟩
    · exact getindexColon_vector_run heap allocated (heap ++ [xs]) src dest _
        heapColonLength (heapColonSimilar layout) heapColonMemoryCopy hlen ha (fun _ => hc)
        (fun hp => by have hz : xs = [] := List.length_eq_zero_iff.mp (by rw [hv] at hp; omega)
                      simp [allocated,hz])
    · intro handle hh
      exact ⟨Nat.ne_of_gt hh, List.getElem?_append_left hh⟩
  · intro hnot
    rw [if_neg hnot] at ha
    simp only [heapColonCopy, getindexColon, vector_bind_run, hlen, ha]
end
end solArray
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayB
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

 theorem assignment_heap_run {Tag α : Type} (heap : VectorHeap α) (a : HeapArray Tag)
    (slots : List (Option α)) (indices : List I) (b : Bool) (k : I)
    (hs : heap[a.handle]? = some slots)
    (hb : heapCheckboundsBool a indices = .ok b)
    (hk : b = true → dimsSub2ind (heapAxes a) indices = .ok k) :
    (isassignedArray (m := VectorM α)
      (fun a is => match heapCheckboundsBool a is with
        | .ok b => pure b | .error _ => throw .bounds)
      (fun a => pure (heapAxes a))
      (fun dims is => match dimsSub2ind dims is with
        | .ok k => pure k | .error _ => throw .bounds)
      (fun a k _ => pure (a.handle,k))
      (fun ref => do
        let xs ← heapSlots ref.1
        pure (match xs[(ref.2.val-1).toNat]? with
          | some (some _) => true | _ => false)) a indices).run heap =
      .ok (b && (match slots[(k.val-1).toNat]? with
        | some (some _) => true | _ => false),heap) := by
  cases b with
  | false =>
    simp only [isassignedArray,vector_bind_run,hb,vector_pure_run,Bool.not_false,ite_true,
      Bool.false_and]
  | true =>
    simp only [isassignedArray,vector_bind_run,hb,vector_pure_run,Bool.not_true,
      Bool.false_eq_true,ite_false,hk rfl,heapSlots_run,hs,Bool.true_and]

 theorem slot_assigned_match (slots : List (Option α)) (k : Int) :
    (match slots[k.toNat]? with | some (some _) => true | _ => false) =
      decide (∃ x, slots[k.toNat]? = some (some x)) := by
  cases h : slots[k.toNat]? with
  | none => simp
  | some value => cases value <;> simp

theorem assigned_nil_bounds_axes (dims : List I) :
    oneToCheckIndices dims [] = .ok (dims.all (fun d => d.val == 1)) := by
  change JuliaLean.base.abstractarray.allTupleM (fun d : I => .ok (d.val == 1)) dims = _
  induction dims with
  | nil => rfl
  | cons d ds ih =>
    cases hd : (d.val == 1) <;>
      simp [JuliaLean.base.abstractarray.allTupleM,hd,ih,Bind.bind,Except.bind,Pure.pure,Except.pure]



theorem assigned_nil_linear (dims : List I) : dimsSub2ind dims [] = .ok one := rfl

theorem assigned_single_linear (dims : List I) (i : I) (hi : 1 ≤ i.val) :
    dimsSub2ind dims [i] = .ok i := by
  have hb := ival_bounds i
  have hs : (i-one).val = i.val-1 := ival_sub_one i (by omega)
  have hm : ((i-one)*one).val = i.val-1 := by
    change (JInt.wrap .i64 ((i-one).val*one.val)).val = _
    rw [hs,ival_one,Int.mul_one,ival_wrap _ (by omega)]
  have he : one+(i-one)*one = i := by
    apply Subtype.ext
    rw [ival_add _ _ (by rw [hm,ival_one]; omega),hm,ival_one]
    omega
  cases dims <;>
    simp only [dimsSub2ind,sub2indRec,JuliaLean.base.abstractarray.sub2indRecurseEmpty,
      JuliaLean.base.abstractarray.sub2indRecurse,JuliaLean.base.abstractarray.sub2indRecurseDone,
      JuliaLean.base.abstractarray.nextLInteger,JuliaLean.base.abstractarray.offsetinInteger,
      List.headD_cons,List.tail_cons,Bind.bind,Except.bind,Pure.pure,Except.pure]
  all_goals exact congrArg Except.ok he
end solArrayB
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayB
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768


open JuliaLean.Proofs.base.int
private def cartesianOffsetInt : List I → List I → Int
  | d :: ds, i :: is => (i.val - 1) + d.val * cartesianOffsetInt ds is
  | _, _ => 0

private theorem sub2indRec_cartesianOffset
    (nextL offsetin : I → I → JuliaLean.base.abstractarray.Result I)
    (hnext : ∀ stride d, nextL stride d = .ok (stride * d))
    (hoff : ∀ i d, offsetin i d = .ok (i - one))
    (dims indices : List I) (stride ind : I)
    (hrank : dims.length = indices.length) :
    sub2indRec nextL offsetin dims stride ind indices =
      .ok (JInt.wrap .i64
        (ind.val + stride.val * cartesianOffsetInt dims indices)) := by
  induction dims generalizing indices stride ind with
  | nil =>
      cases indices with
      | nil =>
          change (Except.ok ind : JuliaLean.base.abstractarray.Result I) =
            .ok (JInt.wrap .i64 (ind.val + stride.val * cartesianOffsetInt [] []))
          simp only [cartesianOffsetInt, Int.mul_zero, Int.add_zero]
          apply congrArg Except.ok
          apply Subtype.ext
          change ind.val = wrapInt .i64 ind.val
          exact (JuliaLean.Proofs.base.int.wrapInt_val ind).symm
      | cons i is => simp at hrank
  | cons d ds ih =>
      cases indices with
      | nil => simp at hrank
      | cons i is =>
          have hrank' : ds.length = is.length := by simp at hrank; omega
          let stride' := stride * d
          let ind' := ind + (i - one) * stride
          have hstep :
              sub2indRec nextL offsetin (d :: ds) stride ind (i :: is) =
                sub2indRec nextL offsetin ds stride' ind' is := by
            simp [sub2indRec, JuliaLean.base.abstractarray.sub2indRecurse,
              hnext, hoff, stride', ind', Bind.bind, Pure.pure,
              Except.bind, Except.pure]
          rw [hstep, ih is stride' ind' hrank']
          apply congrArg Except.ok
          apply Subtype.ext
          change wrapInt .i64
            (wrapInt .i64 (ind.val + wrapInt .i64 (wrapInt .i64 (i.val - one.val) * stride.val)) +
              wrapInt .i64 (stride.val * d.val) * cartesianOffsetInt ds is) = _
          simp only [ival_one, wrapInt_add_left, wrapInt_add_right, wrapInt_mul_left,
            wrapInt_mul_right, cartesianOffsetInt]
          have hcalc :
              ind.val + (i.val - 1) * stride.val +
                  (stride.val * d.val) * cartesianOffsetInt ds is =
                ind.val + stride.val *
                  ((i.val - 1) + d.val * cartesianOffsetInt ds is) := by
            calc
              _ = ind.val + (i.val - 1) * stride.val +
                    stride.val * (d.val * cartesianOffsetInt ds is) := by
                    rw [Int.mul_assoc]
              _ = ind.val + stride.val * (i.val - 1) +
                    stride.val * (d.val * cartesianOffsetInt ds is) := by
                    rw [Int.mul_comm (i.val - 1) stride.val]
              _ = ind.val + (stride.val * (i.val - 1) +
                    stride.val * (d.val * cartesianOffsetInt ds is)) := by
                    rw [Int.add_assoc]
              _ = ind.val + stride.val *
                    ((i.val - 1) + d.val * cartesianOffsetInt ds is) := by
                    rw [← Int.mul_add]
          rw [← wrapInt_add_right .i64
            (ind.val + (i.val - 1) * stride.val)
            (wrapInt .i64 (stride.val * d.val) * cartesianOffsetInt ds is),
            wrapInt_mul_left,wrapInt_add_right,hcalc]
          rfl

private theorem dimsSub2ind_cartesianOffset (dims indices : List I)
    (hrank : dims.length = indices.length) :
    dimsSub2ind dims indices =
      .ok (JInt.wrap .i64 (cartesianOffsetInt dims indices + 1)) := by
  have h := sub2indRec_cartesianOffset
    (fun stride d => JuliaLean.base.abstractarray.nextLInteger
      (fun a b => .ok (a * b)) stride d)
    (fun i d => JuliaLean.base.abstractarray.offsetinInteger
      (fun a b => .ok (a - b)) i d)
    (by intros; rfl) (by intros; rfl) dims indices one one hrank
  simpa only [dimsSub2ind, ival_one, Int.one_mul, Int.add_comm] using h
private theorem cartesianOffsetInt_heapAxes (dims : List Nat) (indices : List I)
    (hfit : heapDimensionsFit dims = true) (hrank : dims.length = indices.length) :
    cartesianOffsetInt (dims.map (fun (d : Nat) => JInt.wrap .i64 (d : Int))) indices =
      cartesianOffset dims indices := by
  induction dims generalizing indices with
  | nil =>
      cases indices with
      | nil => rfl
      | cons i is => simp at hrank
  | cons d ds ih =>
      cases indices with
      | nil => simp at hrank
      | cons i is =>
          have hfitParts : d < 2 ^ 63 ∧ heapDimensionsFit ds = true := by
            simpa [heapDimensionsFit] using hfit
          have hrank' : ds.length = is.length := by simp at hrank; omega
          have hd : (JInt.wrap .i64 (d : Int)).val = d := ival_wrap _ (by omega)
          simp [cartesianOffsetInt, cartesianOffset, hd,
            ih is hfitParts.2 hrank']

private theorem cartesianOffset_bounds (dims : List Nat) (indices : List I)
    (hrank : dims.length = indices.length)
    (hbound : cartesianInBounds dims indices = true) :
    0 ≤ cartesianOffset dims indices ∧ cartesianOffset dims indices < dims.prod := by
  induction dims generalizing indices with
  | nil =>
      cases indices with
      | nil => simp [cartesianOffset]
      | cons i is => simp at hrank
  | cons d ds ih =>
      cases indices with
      | nil => simp at hrank
      | cons i is =>
          have hrank' : ds.length = is.length := by simp at hrank; omega
          have hparts : (1 ≤ i.val ∧ i.val ≤ (d : Int)) ∧
              cartesianInBounds ds is = true := by
            simpa [cartesianInBounds, Bool.and_eq_true, decide_eq_true_eq] using hbound
          obtain ⟨ht0, htt⟩ := ih is hrank' hparts.2
          have hdpos : 0 < (d : Int) := by omega
          have hhead : 0 ≤ i.val - 1 ∧ i.val - 1 < (d : Int) := by omega
          have htaille : cartesianOffset ds is + 1 ≤ ds.prod := by omega
          have hprod : ((d :: ds).prod : Int) = (d : Int) * ds.prod := by simp
          constructor
          · rw [cartesianOffset]
            exact Int.add_nonneg hhead.1 (Int.mul_nonneg (by omega) ht0)
          · rw [cartesianOffset, hprod]
            calc
              i.val - 1 + (d : Int) * cartesianOffset ds is <
                  (d : Int) + (d : Int) * cartesianOffset ds is := by omega
              _ = (d : Int) * (cartesianOffset ds is + 1) := by
                    rw [Int.mul_add, Int.mul_one, Int.add_comm]
              _ ≤ (d : Int) * ds.prod :=
                Int.mul_le_mul_of_nonneg_left htaille (by omega : (0 : Int) ≤ d)

private theorem checkindexOneTo_i64_bounds (last index : JInt .i64)
    (hnonneg : 0 ≤ last.val) :
    JuliaLean.base.abstractarray.checkindexOneTo last index = true ↔
      1 ≤ index.val ∧ index.val ≤ last.val := by
  have indexRange := ival_bounds index
  have lastRange := ival_bounds last
  change (decide (wrapInt .u64 (wrapInt .i64 (index.val - 1)) <
    wrapInt .u64 last.val) = true ↔ _)
  have hm : wrapInt .u64 (wrapInt .i64 (index.val - 1)) =
      (index.val - 1) % 18446744073709551616 :=
    wrapInt_emod_self .i64 (index.val - 1)
  have hl : wrapInt .u64 last.val = last.val :=
    wrapInt_of_inRange .u64 last.val (by
      change 0 ≤ last.val ∧ last.val ≤ 18446744073709551615
      omega)
  rw [hm,hl]
  simp only [decide_eq_true_eq]
  omega
end solArrayB
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace solArrayB
open JuliaLean JuliaLean.base.array
open JuliaLean.Proofs.base.array.round4
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768


open JuliaLean.Proofs.base.int

attribute [local irreducible] JInt.wrap wrapInt

theorem assigned_bounds_cons (d i : I) (ds is : List I) :
    oneToCheckIndices (d :: ds) (i :: is) =
      if JuliaLean.base.abstractarray.checkindexOneTo d i then oneToCheckIndices ds is else .ok false := rfl

theorem assigned_checkindex_nat (d : Nat) (i : I) (hd : d < 2 ^ 63) :
    JuliaLean.base.abstractarray.checkindexOneTo (JInt.wrap .i64 d) i =
      decide (1 ≤ i.val ∧ i.val ≤ (d : Int)) := by
  have hv : (JInt.wrap .i64 (d : Int)).val = d := ival_wrap _ (by omega)
  have hc := checkindexOneTo_i64_bounds (JInt.wrap .i64 (d : Int)) i (by rw [hv]; omega)
  rw [hv] at hc
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hc)

set_option maxRecDepth 32768 in
private theorem oneToCheckIndices_cartesian (dims : List Nat) (indices : List I)
    (hfit : heapDimensionsFit dims = true) (hrank : dims.length = indices.length) :
    oneToCheckIndices (dims.map (fun n => JInt.wrap .i64 (Int.ofNat n))) indices =
      .ok (cartesianInBounds dims indices) := by
  induction dims generalizing indices with
  | nil =>
    cases indices with
    | nil => rfl
    | cons i is => simp only [List.length_nil,List.length_cons] at hrank; omega
  | cons d ds ih =>
    cases indices with
    | nil => simp only [List.length_nil,List.length_cons] at hrank; omega
    | cons i is =>
      have hp : d < 2 ^ 63 ∧ heapDimensionsFit ds = true := by
        simpa only [heapDimensionsFit,List.all_cons,Bool.and_eq_true,decide_eq_true_eq] using hfit
      have he := assigned_checkindex_nat d i hp.1
      have hr : ds.length = is.length := by
        simp only [List.length_cons] at hrank
        omega
      have hi := ih is hp.2 hr
      rw [List.map_cons,assigned_bounds_cons]
      erw [he,hi]
      change (if decide (1 ≤ i.val ∧ i.val ≤ (d : Int)) then
        (Except.ok (cartesianInBounds ds is) : JuliaLean.base.abstractarray.Result Bool)
        else Except.ok false) = _
      rw [cartesianInBounds]
      cases hb : decide (1 ≤ i.val ∧ i.val ≤ (d : Int)) with
      | false => rfl
      | true => rfl

theorem assigned_bounds_single {Tag : Type} (a : HeapArray Tag) (i : I)
    (hprod : a.dimensions.prod < 2 ^ 62) :
    heapCheckboundsBool a [i] =
      .ok (decide (1 ≤ i.val ∧ i.val ≤ (a.dimensions.prod : Int))) := by
  have hv : (JInt.wrap .i64 (a.dimensions.prod : Int)).val = a.dimensions.prod :=
    ival_wrap _ (by omega)
  have hc := checkindexOneTo_i64_bounds (JInt.wrap .i64 (a.dimensions.prod : Int)) i (by rw [hv]; omega)
  simp only [heapCheckboundsBool, JuliaLean.base.abstractarray.checkboundsOne,
    Bind.bind, Except.bind]
  apply congrArg Except.ok
  apply Bool.eq_iff_iff.mpr
  simpa only [hv, decide_eq_true_eq] using hc

theorem assigned_axes_nil (dims : List Nat) (hfit : heapDimensionsFit dims = true) :
    (dims.map (fun (d : Nat) => JInt.wrap .i64 d)).all (fun d => d.val == 1) =
      dims.all (fun d => d == 1) := by
  induction dims with
  | nil => rfl
  | cons d ds ih =>
    have hp : d < 2 ^ 63 ∧ heapDimensionsFit ds = true := by simpa [heapDimensionsFit] using hfit
    have hv : (JInt.wrap .i64 (d : Int)).val = d := ival_wrap _ (by omega)
    have he : ((d : Int) == 1) = (d == 1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq]
      omega
    simp only [List.map_cons,List.all_cons,hv,he,ih hp.2]

theorem assignmentLinearArraySpec : round4.AssignmentLinearArraySpec := by
  intro Tag α heap a slots hs
  dsimp only [round4.AssignmentLinearArraySpec]
  refine ⟨?_, ?_, ?_⟩
  · intro indices hrank htwo
    have hb : heapCheckboundsBool a indices = .ok (cartesianInBounds a.dimensions indices) := by
      cases indices with
      | nil => simp at htwo
      | cons i is =>
        cases is with
        | nil => simp at htwo
        | cons j js =>
          change oneToCheckIndices (heapAxes a) (i :: j :: js) = _
          exact oneToCheckIndices_cartesian a.dimensions _ hs.2.2.1 hrank.symm
    let k : I := JInt.wrap .i64 (cartesianOffset a.dimensions indices + 1)
    have hk : dimsSub2ind (heapAxes a) indices = .ok k := by
      rw [dimsSub2ind_cartesianOffset]
      · change Except.ok (JInt.wrap .i64 (cartesianOffsetInt
          (a.dimensions.map (fun (d : Nat) => JInt.wrap .i64 d)) indices + 1)) = _
        rw [cartesianOffsetInt_heapAxes _ _ hs.2.2.1 hrank.symm]
      · simpa [heapAxes] using hrank.symm
    have hh := assignment_heap_run heap a slots indices
      (cartesianInBounds a.dimensions indices) k hs.1 hb (fun _ => hk)
    erw [hh]
    cases hc : cartesianInBounds a.dimensions indices with
    | false => rfl
    | true =>
      have ho := cartesianOffset_bounds _ _ hrank.symm hc
      have hprod := hs.2.2.2
      have hv : k.val - 1 = cartesianOffset a.dimensions indices := by
        dsimp [k]
        rw [ival_wrap _ (by omega)]
        omega
      simp only [Bool.true_and, hv, slot_assigned_match]
  · intro i
    let b := decide (1 ≤ i.val ∧ i.val ≤ (a.dimensions.prod : Int))
    have hb := assigned_bounds_single a i hs.2.2.2
    have hh := assignment_heap_run heap a slots [i] b i hs.1 hb
      (fun h => assigned_single_linear _ i ((of_decide_eq_true h).1))
    erw [hh]
    simp only [slot_assigned_match]
    rfl
  · have hb : heapCheckboundsBool a [] =
        .ok (a.dimensions.all (fun d => d == 1)) := by
      change oneToCheckIndices (heapAxes a) [] = _
      rw [assigned_nil_bounds_axes]
      exact congrArg Except.ok (assigned_axes_nil _ hs.2.2.1)
    have hh := assignment_heap_run heap a slots [] (a.dimensions.all (fun d => d == 1))
      one hs.1 hb (fun _ => rfl)
    erw [hh]
    simp only [ival_one,Int.sub_self,slot_assigned_match]
end solArrayB
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
namespace ChatGPTBatch1.ArrayRange
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.Proofs.base.array.round4

attribute [local irreducible] JInt.wrap wrapInt

/-- The range bounds call used by the frozen property. -/
def batch1_rangeBounds {Tag α : Type} (f l : IntegerValue) (a : HeapArray Tag) : VectorM α Unit := do
  let n ← heapArrayLength a
  let check := JuliaLean.base.abstractarray.checkboundsOne (fun _ => .ok n)
    (JuliaLean.base.abstractarray.checkindexRange (fun (_ : Unit) => .ok (decide (l.val < f.val)))
      (fun _ => .ok f) (fun _ => .ok l)
      (JuliaLean.base.abstractarray.checkindexReal (fun _ : I => .ok one) (fun n : I => .ok n)
        (fun lo (i : IntegerValue) => .ok (decide (lo.val ≤ i.val)))
        (fun (i : IntegerValue) hi => .ok (decide (i.val ≤ hi.val))))) a ()
  match check with
  | .ok true => pure ()
  | _ => throw .bounds

def batch1_rangeRun {Tag α : Type} (layout : Tag → Option MemoryLayout) (ops : BigIntegerOps)
    (a : HeapArray Tag) (f l len : IntegerValue) : VectorM α (HeapArray Tag) :=
  getindexUnitRange (fun x : IntegerValue => pure (decide (x.val > 0)))
    (fun a (_ : Unit) => batch1_rangeBounds f l a) (fun _ => pure len) (fun _ => pure len)
    (fun (a : HeapArray Tag) (n : IntegerValue) => do
      match n.toInt ops with
      | .ok k => heapVectorAllocate layout a.elementType k
      | .error e => throw e)
    (fun _ => pure one) (fun _ => pure f)
    (fun x xi src si n => do
      let _ ← copyto288 (heapCopyImpl α Tag ops (fun x => .ok x)) x (.ofInt xi) src si n
      pure ()) a ()

theorem batch1_rangeBounds_run {Tag α : Type} (heap : VectorHeap α) (a : HeapArray Tag)
    (xs : List (Option α)) (hs : heap[a.handle]? = some xs) (hn : xs.length < 2 ^ 63)
    (f l : IntegerValue) :
    (batch1_rangeBounds f l a).run heap =
      if l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int)) then .ok ((), heap)
      else .error .bounds := by
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := ival_wrap _ (by omega)
  have hbool : (decide (l.val < f.val) ||
      ((decide (one.val ≤ f.val) && decide (f.val ≤ (JInt.wrap .i64 (xs.length : Int)).val)) &&
       (decide (one.val ≤ l.val) && decide (l.val ≤ (JInt.wrap .i64 (xs.length : Int)).val)))) =
      decide (l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [ival_one, hv]
    omega
  simp only [batch1_rangeBounds, heapArrayLength, vector_bind_run, heapLength_run, hs]
  simp only [JuliaLean.base.abstractarray.checkboundsOne,
    JuliaLean.base.abstractarray.checkindexRange, JuliaLean.base.abstractarray.checkindexReal,
    Bind.bind, Pure.pure, Except.bind, Except.pure, hbool]
  by_cases hg : l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int))
  · simp only [hg, decide_true, ite_true]
    rfl
  · simp only [hg, decide_false, ite_false]
    rfl

/-- Conversions of all integer argument families agree when the represented value fits Int. -/
theorem batch1_integer_toInt {ops : BigIntegerOps} (ho : ops.Lawful)
    (v : IntegerValue) (i : I) (hi : v.val = i.val) : v.toInt ops = .ok i := by
  rw [opusGrowth.integerValue_toInt ho]
  rw [if_pos (by rw [hi]; exact i.property)]
  apply congrArg Except.ok
  exact Subtype.ext (by rw [ival_wrap _ (by rw [hi]; exact i.property), hi])

theorem batch1_heapCheckLinear_fromLength {Tag α : Type} (ops : BigIntegerOps)
    (ho : ops.Lawful) (heap : VectorHeap α) (a : HeapArray Tag) (n : I)
    (hlinear : (heapLinearIndices a).run heap =
      .ok ((⟨n⟩ : JuliaLean.base.range.OneTo I), heap))
    (i : IntegerValue) (hi : 1 ≤ i.val ∧ i.val ≤ n.val) :
    (heapCheckLinear ops a i).run heap = .ok ((), heap) := by
  have hlast : JuliaLean.base.range.last_OrdinalRange (T := I) (A := I)
      (⟨n⟩ : JuliaLean.base.range.OneTo I) = .ok n :=
    JuliaLean.Proofs.base.range.last_oneTo _
  have hone : (JuliaLean.base.range.JOneunit.oneunit : I).val = 1 := by
    change (JInt.wrap .i64 1).val = 1
    exact ival_wrap _ (by omega)
  have hlo : IntegerValue.intLe ops (JuliaLean.base.range.JOneunit.oneunit : I) i = true := by
    rw [batch1_integer_intLe ops ho]
    exact decide_eq_true (by rw [hone]; exact hi.1)
  have hhi : IntegerValue.leInt ops i n = true := by
    rw [batch1_integer_leInt ops ho]
    exact decide_eq_true hi.2
  simp only [heapCheckLinear, vector_bind_run, hlinear]
  simp only [JuliaLean.base.abstractarray.checkindexReal,
    JuliaLean.base.range.first_OneTo, hlast, Bind.bind, Pure.pure, Except.bind,
    Except.pure, hlo, hhi, Bool.true_and]
  rfl

/-- Linear bounds use the actual heap length. -/
theorem batch1_heapCheckLinear_ok {Tag α : Type} (ops : BigIntegerOps) (ho : ops.Lawful)
    (heap : VectorHeap α) (a : HeapArray Tag) (xs : List (Option α))
    (hs : heap[a.handle]? = some xs) (hn : xs.length < 2 ^ 63)
    (i : IntegerValue) (hi : 1 ≤ i.val ∧ i.val ≤ (xs.length : Int)) :
    (heapCheckLinear ops a i).run heap = .ok ((), heap) := by
  have hv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := ival_wrap _ (by omega)
  have hlinear : (heapLinearIndices a).run heap =
      .ok ((⟨JInt.wrap .i64 (xs.length : Int)⟩ : JuliaLean.base.range.OneTo I), heap) := by
    simp only [heapLinearIndices, JuliaLean.base.abstractarray.eachindexDense,
      heapArrayLength, vector_bind_run, heapLength_run, hs, vector_pure_run]
  exact batch1_heapCheckLinear_fromLength ops ho heap a _ hlinear i (by rw [hv]; exact hi)

theorem batch1_vectorStateLift_run (value : Except Error β) (heap : VectorHeap α) :
    (StateT.lift value : VectorM α β).run heap = value.map (fun x => (x, heap)) := by
  cases value <;> rfl

theorem batch1_remaining_val (N : Nat) (i : Int) (hN : N < 2 ^ 63)
    (hi : 1 ≤ i ∧ i ≤ (N : Int)) :
    (JInt.wrap .i64 ((JInt.wrap .i64 (N : Int)).val - i) + one).val =
      (N : Int) - i + 1 := by
  have hvN : (JInt.wrap .i64 (N : Int)).val = N := ival_wrap _ (by omega)
  have hd : (JInt.wrap .i64 ((N : Int) - i)).val = (N : Int) - i :=
    ival_wrap _ (by omega)
  rw [hvN]
  rw [ival_add (JInt.wrap .i64 ((N : Int) - i)) one
    (by rw [hd, ival_one]; omega), hd, ival_one]

/-- Checked copying on valid positive windows, for arbitrary integer argument types. -/
theorem batch1_heapCopyImpl_window {Tag α : Type} (ops : BigIntegerOps) (ho : ops.Lawful)
    (heap : VectorHeap α) (dest src : HeapArray Tag) (xs ys : List (Option α))
    (hx : heap[dest.handle]? = some xs) (hy : heap[src.handle]? = some ys)
    (hxn : xs.length < 2 ^ 63) (hyn : ys.length < 2 ^ 63)
    (di si len : IntegerValue) (hn : 0 < len.val)
    (hd : 1 ≤ di.val ∧ di.val - 1 + len.val ≤ (xs.length : Int))
    (hs : 1 ≤ si.val ∧ si.val - 1 + len.val ≤ (ys.length : Int)) :
    (heapCopyImpl α Tag ops (fun x => .ok x) dest di src si len).run heap =
      .ok (dest, heap.set dest.handle (xs.take (di.val - 1).toNat ++
        (ys.drop (si.val - 1).toNat).take len.val.toNat ++ xs.drop (di.val - 1 + len.val).toNat)) := by
  have hdiBound : di.val ≤ (xs.length : Int) := by omega
  have hsiBound : si.val ≤ (ys.length : Int) := by omega
  have hn0 : ¬ len.val = 0 := by omega
  have hdf : len.val ≤ (xs.length : Int) - di.val + 1 := by omega
  have hsf : len.val ≤ (ys.length : Int) - si.val + 1 := by omega
  have hrd := batch1_remaining_val xs.length di.val hxn ⟨hd.1, hdiBound⟩
  have hrs := batch1_remaining_val ys.length si.val hyn ⟨hs.1, hsiBound⟩
  let d := JInt.wrap .i64 di.val
  let s := JInt.wrap .i64 si.val
  let n := JInt.wrap .i64 len.val
  have hdv : d.val = di.val := ival_wrap _ (by omega)
  have hsv : s.val = si.val := ival_wrap _ (by omega)
  have hnv : n.val = len.val := ival_wrap _ (by omega)
  have hdi := batch1_integer_toInt ho di d hdv.symm
  have hsi := batch1_integer_toInt ho si s hsv.symm
  have hni := batch1_integer_toInt ho len n hnv.symm
  have hdb := batch1_heapCheckLinear_ok ops ho heap dest xs hx hxn di (by omega)
  have hsb := batch1_heapCheckLinear_ok ops ho heap src ys hy hyn si (by omega)
  have hdl : (heapArrayLength dest).run heap = .ok (JInt.wrap .i64 (xs.length : Int), heap) := by
    simp only [heapArrayLength, heapLength_run, hx]
  have hsl : (heapArrayLength src).run heap = .ok (JInt.wrap .i64 (ys.length : Int), heap) := by
    simp only [heapArrayLength, heapLength_run, hy]
  have hxv : (JInt.wrap .i64 (xs.length : Int)).val = xs.length := ival_wrap _ (by omega)
  have hyv : (JInt.wrap .i64 (ys.length : Int)).val = ys.length := ival_wrap _ (by omega)
  have hcopy := heapCopyReferences_window_run heap dest.handle src.handle ys xs hy hx d s n
    (by rw [hnv]; omega) (by rw [hdv]; exact hd.1)
    (by rw [hdv, hnv]; exact hd.2) (by rw [hsv]; exact hs.1)
    (by rw [hsv, hnv]; exact hs.2)
  rw [hdv, hsv, hnv] at hcopy
  simp only [heapCopyImpl, copytoImpl, vector_bind_run, vector_pure_run, hn0,
    decide_false, Bool.false_eq_true, ite_false, hn, decide_true, Bool.not_true,
    hdb, hsb, hdl, hsl, hrd, hrs, hdf, hsf, hdi, hsi, hni, heapReference, hcopy,
    batch1_vectorStateLift_run, Except.map]


/-- The one-dimensional allocator, expressed using its documented size condition. -/
theorem batch1_vectorAllocate_run {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (el : MemoryLayout) (tag : Tag) (hl : layout tag = some el)
    (heap : VectorHeap α) (n : I) (hn : 0 ≤ n.val) :
    (heapVectorAllocate layout tag n).run heap =
      if memoryFits el n.val.toNat then
        .ok (⟨heap.length, tag, [n.val.toNat], [(1, n.val.toNat)]⟩,
          heap ++ [List.replicate n.val.toNat none])
      else .error (.argument genericMemorySizeMessage) := by
  rw [heapVectorAllocate, opusGrowth.heapArrayUndef_run layout tag el hl]
  simp only [allocOutcome, arrayAllocError, List.map_cons, List.map_nil,
    show ¬ n.val < 0 from by omega, false_or, List.prod_cons, List.prod_nil, Nat.mul_one]
  by_cases hf : memoryFits el n.val.toNat
  · simp only [hf, not_true_eq_false, ite_false, ite_true]
  · simp only [hf, not_false_eq_true, ite_true, ite_false]

/-- The complete successful-bounds path for a range whose length is exact. -/
theorem batch1_rangeRun_good {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (el : MemoryLayout) (ops : BigIntegerOps) (heap : VectorHeap α) (a : HeapArray Tag)
    (xs : List (Option α)) (f l len : IntegerValue)
    (hlayout : layout a.elementType = some el) (ho : ops.Lawful)
    (hs : heap[a.handle]? = some xs) (hn : xs.length < 2 ^ 63)
    (hnormal : f.val - 1 ≤ l.val)
    (hgood : l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int)))
    (hlen : len.val = l.val - f.val + 1) :
    let window := (xs.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat
    (batch1_rangeRun layout ops a f l len).run heap =
      if memoryFits el window.length then
        .ok (⟨heap.length, a.elementType, [window.length], [(1, window.length)]⟩, heap ++ [window])
      else .error (.argument genericMemorySizeMessage) := by
  intro window
  have hlen0 : 0 ≤ len.val := by omega
  have hlenle : len.val ≤ (xs.length : Int) := by rcases hgood with h | h <;> omega
  have hwlen : window.length = len.val.toNat := by
    simp only [window, List.length_take, List.length_drop]
    rcases hgood with he | hi
    · have he0 : l.val - f.val + 1 = 0 := by omega
      rw [he0]
      simp only [Int.toNat_zero, Nat.zero_min]
      omega
    · omega
  let n : I := JInt.wrap .i64 len.val
  have hnv : n.val = len.val := ival_wrap _ (by omega)
  have hconv := batch1_integer_toInt ho len n hnv.symm
  have hbounds := batch1_rangeBounds_run heap a xs hs hn f l
  rw [if_pos hgood] at hbounds
  have halloc := batch1_vectorAllocate_run layout el a.elementType hlayout heap n
    (by rw [hnv]; exact hlen0)
  rw [hnv, ← hwlen] at halloc
  by_cases hf : memoryFits el window.length
  · rw [if_pos hf]
    rw [if_pos hf] at halloc
    let dest : HeapArray Tag := ⟨heap.length, a.elementType, [window.length], [(1, window.length)]⟩
    let init := heap ++ [List.replicate window.length (none : Option α)]
    have hione : (IntegerValue.ofInt one).val = 1 := ival_one
    by_cases hp : 0 < len.val
    · have hfi : 1 ≤ f.val ∧ f.val ≤ l.val ∧ l.val ≤ (xs.length : Int) := by
        rcases hgood with he | hi <;> omega
      have hsrc : init[a.handle]? = some xs := by
        rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp hs).choose)]
        exact hs
      have hdest : init[dest.handle]? = some (List.replicate window.length none) := by
        simp only [dest, init, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
      have hcopy := batch1_heapCopyImpl_window ops ho init dest a
        (List.replicate window.length none) xs hdest hsrc
        (by simp only [List.length_replicate]; rw [hwlen]; omega) hn
        (.ofInt one) f len hp
        (by
          simp only [hione, List.length_replicate]
          rw [hwlen]
          omega) (by omega)
      have hw : (List.replicate window.length (none : Option α)).take
            ((IntegerValue.ofInt one).val - 1).toNat ++
          (xs.drop (f.val - 1).toNat).take len.val.toNat ++
          (List.replicate window.length none).drop
            ((IntegerValue.ofInt one).val - 1 + len.val).toNat = window := by
        simp only [hione,
          show ((1 : Int) - 1).toNat = 0 from rfl, Int.sub_self, Int.zero_add,
          Int.toNat_zero, List.take_zero, List.nil_append]
        rw [← hwlen, List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil]
        rw [hwlen, hlen]
      rw [hw] at hcopy
      have hset : init.set dest.handle window = heap ++ [window] := by
        change (heap ++ [List.replicate window.length none]).set heap.length window = _
        rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [hset] at hcopy
      dsimp only [dest, init] at hcopy
      simp only [batch1_rangeRun, getindexUnitRange, vector_bind_run, hbounds,
        vector_pure_run, hconv, halloc, hp, decide_true, ite_true, copyto288, hcopy]
    · have hz : len.val = 0 := by omega
      have hwz : window = [] := List.length_eq_zero_iff.mp (by rw [hwlen, hz]; rfl)
      simp only [batch1_rangeRun, getindexUnitRange, vector_bind_run, hbounds,
        vector_pure_run, hconv, halloc, hp, decide_false, Bool.false_eq_true, ite_false]
      rw [hwz]
      rfl
  · rw [if_neg hf]
    rw [if_neg hf] at halloc
    simp only [batch1_rangeRun, getindexUnitRange, vector_bind_run, hbounds,
      vector_pure_run, hconv, halloc]

/-- The frozen range postcondition follows once a lawful range's length is supplied. -/
theorem batch1_rangeGetindexOn {Tag α : Type} (layout : Tag → Option MemoryLayout)
    (el : MemoryLayout) (ops : BigIntegerOps) (heap : VectorHeap α) (a : HeapArray Tag)
    (xs : List (Option α)) (f l len : IntegerValue)
    (hlayout : layout a.elementType = some el) (ho : ops.Lawful)
    (hs : heap[a.handle]? = some xs) (hn : xs.length < 2 ^ 63)
    (hnormal : f.val - 1 ≤ l.val)
    (hlen : (l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int))) →
      len.val = l.val - f.val + 1) : RangeGetindexOn layout el ops heap a xs f l len := by
  change (f.val ≤ l.val → ¬(1 ≤ f.val ∧ l.val ≤ (xs.length : Int)) →
      (batch1_rangeRun layout ops a f l len).run heap = .error .bounds) ∧
    ((l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int))) →
      memoryFits el ((xs.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat).length →
      ∃ b, (batch1_rangeRun layout ops a f l len).run heap =
        .ok (b, heap ++ [(xs.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat]) ∧
        b.handle = heap.length ∧ b.dimensions =
          [((xs.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat).length]) ∧
    (1 ≤ f.val → f.val ≤ l.val → l.val ≤ (xs.length : Int) →
      ¬ memoryFits el ((xs.drop (f.val - 1).toNat).take (l.val - f.val + 1).toNat).length →
      (batch1_rangeRun layout ops a f l len).run heap =
        .error (.argument genericMemorySizeMessage))
  refine ⟨?_, ?_, ?_⟩
  · intro hf hl
    have hb := batch1_rangeBounds_run heap a xs hs hn f l
    rw [if_neg (by omega)] at hb
    simp only [batch1_rangeRun, getindexUnitRange, vector_bind_run, hb]
  · intro hg hfit
    have hr := batch1_rangeRun_good layout el ops heap a xs f l len hlayout ho hs hn
      hnormal hg (hlen hg)
    dsimp only at hr
    rw [if_pos hfit] at hr
    exact ⟨_, hr, rfl, rfl⟩
  · intro hf hfl hl hfit
    have hg : l.val < f.val ∨ (1 ≤ f.val ∧ l.val ≤ (xs.length : Int)) := Or.inr ⟨hf, hl⟩
    have hr := batch1_rangeRun_good layout el ops heap a xs f l len hlayout ho hs hn
      hnormal hg (hlen hg)
    dsimp only at hr
    rw [if_neg hfit] at hr
    exact hr


/-- Normalized in-bounds machine-integer unit ranges have their exact nonnegative length. -/
theorem batch1_unitRange_length (t : IntTy) (r : JuliaLean.base.range.UnitRange (JInt t))
    (N : Nat) (hN : N < 2 ^ 63) (hr : r.start.val - 1 ≤ r.stop.val)
    (hg : r.stop.val < r.start.val ∨ (1 ≤ r.start.val ∧ r.stop.val ≤ (N : Int))) :
    ∃ n : JInt (JuliaLean.Proofs.base.range.lenTy t),
      JuliaLean.Proofs.base.range.lengthUnit r = .ok n ∧
        n.val = r.stop.val - r.start.val + 1 := by
  have hmax : 9223372036854775807 ≤ (JuliaLean.Proofs.base.range.lenTy t).max := by
    cases t <;> decide
  have hcnt : JuliaLean.Proofs.base.range.cnt r.start.val r.stop.val =
      r.stop.val - r.start.val + 1 := by
    unfold JuliaLean.Proofs.base.range.cnt
    split <;> omega
  have hfit : JuliaLean.Proofs.base.range.cnt r.start.val r.stop.val ≤
      (JuliaLean.Proofs.base.range.lenTy t).max := by
    rw [hcnt]
    rcases hg with hg | hg <;> omega
  have hstop : JuliaLean.Proofs.base.range.unitStop r.start r.stop = r.stop := by
    apply Subtype.ext
    rw [JuliaLean.Proofs.base.range.unitStop_val]
    split <;> omega
  obtain ⟨n, hrun, hv⟩ := JuliaLean.Proofs.base.range.lengthUnit_fits r.start r.stop hfit
  rw [hstop] at hrun
  exact ⟨n, hrun, hv.trans hcnt⟩

/-- Every unit-range family in the frozen contract selects exactly the requested heap window. -/
theorem MultidimcovArrayV2GetindexUnitrange_proven :
    JuliaLean.Proofs.base.array.round4.RangeGetindexSpec := by
  intro Tag α layout el ops heap a xs hlayout ho hs hn
  refine ⟨?_, ?_, ?_⟩
  · intro t r hr
    apply batch1_rangeGetindexOn layout el ops heap a xs (.bit t r.start) (.bit t r.stop)
      (match JuliaLean.Proofs.base.range.lengthUnit r with
       | .ok n => .bit _ n
       | .error _ => .bit .i64 zero) hlayout ho hs hn hr
    intro hg
    obtain ⟨n, hrun, hv⟩ := batch1_unitRange_length t r xs.length hn hr hg
    rw [hrun]
    exact hv
  · intro t r hr
    have hfirst : (JInt.wrap t 1).val = 1 := by
      unfold JInt.wrap
      exact wrapInt_of_inRange t 1 (by cases t <;> decide)
    apply batch1_rangeGetindexOn layout el ops heap a xs (.bit t (JInt.wrap t 1)) (.bit t r.stop)
      (match JuliaLean.Proofs.base.range.lengthOneTo r with
       | .ok n => .bit _ n
       | .error _ => .bit .i64 zero) hlayout ho hs hn
      (by change (JInt.wrap t 1).val - 1 ≤ r.stop.val; rw [hfirst]; omega)
    intro _
    have hv := JuliaLean.Proofs.base.range.lengthOneTo_val r.stop hr
    cases hk : JuliaLean.Proofs.base.range.lengthOneTo r with
    | error e =>
      rw [hk] at hv
      cases hv
    | ok n =>
      rw [hk] at hv
      change Except.ok n.val = Except.ok r.stop.val at hv
      have hnval : n.val = r.stop.val := Except.ok.inj hv
      change n.val = r.stop.val - (JInt.wrap t 1).val + 1
      rw [hnval, hfirst]
      omega
  · intro f l _ _ hr
    exact batch1_rangeGetindexOn layout el ops heap a xs f l (.big (l.val - f.val + 1))
      hlayout ho hs hn hr (fun _ => rfl)
end ChatGPTBatch1.ArrayRange
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
namespace ChatGPTBatch1.ArrayAssignment
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

attribute [local irreducible] JInt.wrap wrapInt

/-- The frame preserved by writes to one backing memory. -/
def batch1_arrayFrame (initial next : MutableMemory α) (mem : Nat) : Prop :=
  next.arrays = initial.arrays ∧
    ∀ other, mem ≠ other → next.memories[other]? = initial.memories[other]?

theorem batch1_arrayFrame_refl (s : MutableMemory α) (mem : Nat) :
    batch1_arrayFrame s s mem := ⟨rfl, fun _ _ => rfl⟩

theorem batch1_arrayFrame_trans {s s' s'' : MutableMemory α} {mem : Nat}
    (h : batch1_arrayFrame s s' mem) (h' : batch1_arrayFrame s' s'' mem) :
    batch1_arrayFrame s s'' mem := by
  exact ⟨h'.1.trans h.1, fun other ho => (h'.2 other ho).trans (h.2 other ho)⟩

theorem batch1_arrayFrame_set (s : MutableMemory α) (mem : Nat) (slots : List (Option α)) :
    batch1_arrayFrame s {s with memories := s.memories.set mem slots} mem := by
  refine ⟨rfl, ?_⟩
  intro other h
  exact List.getElem?_set_ne h

/-- A source on a distinct backing memory remains the same vector window. -/
theorem batch1_arrayFrame_vecAt {s s' : MutableMemory α} {mem handle sourceMem : Nat}
    {off n : I} {slots : List (Option α)}
    (h : batch1_arrayFrame s s' mem) (v : VecAt s handle sourceMem off n slots)
    (hne : mem ≠ sourceMem) : VecAt s' handle sourceMem off n slots := by
  refine ⟨?_, ?_, v.2.2⟩
  · rw [h.1]
    exact v.1
  · rw [h.2 sourceMem hne]
    exact v.2.1

/-- One legal indexed write preserves the vector and all unrelated memory. -/
theorem batch1_arrayStore {s : MutableMemory α} {a mem : Nat} {off n : I}
    {slots : List (Option α)} (v : VecAt s a mem off n slots) (i : I) (x : α)
    (hi : 1 ≤ i.val ∧ i.val ≤ n.val) :
    ∃ next slots', (mutableSet a x i).run s = (.ok (), next) ∧
      batch1_arrayFrame s next mem ∧ VecAt next a mem off n slots' ∧
      next.contents a = (s.contents a).set (i.val - 1).toNat (some x) := by
  let next := {s with memories := s.memories.set mem (slots.set
    (off.val - 1 + i.val - 1).toNat (some x))}
  have hv := v.set (off.val - 1 + i.val - 1).toNat (some x)
  refine ⟨next, _, vwSet_run s a mem off n slots v i hi x,
    batch1_arrayFrame_set _ _ _, hv, ?_⟩
  rw [hv.contents, v.contents]
  exact vwWindow_set slots off n i (some x) v.2.2.1 hi.1

theorem batch1_storeAll_length (ys : List (Option α)) (pairs : List (I × α)) :
    (storeAll ys pairs).length = ys.length := by
  induction pairs generalizing ys with
  | nil => rfl
  | cons q qs ih =>
    change (storeAll (ys.set (q.1.val - 1).toNat (some q.2)) qs).length = _
    rw [ih, List.length_set]

theorem batch1_lastStored_cons (q : I × α) (qs : List (I × α)) (p : Nat) :
    lastStored (q :: qs) p =
      match lastStored qs p with
      | some x => some x
      | none => if q.1.val = (p : Int) + 1 then some q.2 else none := by
  simp only [lastStored, List.reverse_cons, List.find?_append]
  cases hf : qs.reverse.find? (fun q => decide (q.1.val = (p : Int) + 1)) with
  | none =>
    by_cases hq : q.1.val = (p : Int) + 1
    · simp only [Option.none_or, Option.map_none, List.find?_cons, List.find?_nil,
        hq, decide_true, ite_true, Option.map_some]
    · simp only [Option.none_or, Option.map_none, List.find?_cons, List.find?_nil,
        hq, decide_false, Bool.false_eq_true, ite_false]
  | some value => rfl

/-- Repeated indices retain their last assigned value. -/
theorem batch1_storeAll_get (ys : List (Option α)) (pairs : List (I × α))
    (hpos : ∀ q ∈ pairs, 1 ≤ q.1.val) (p : Nat) (hp : p < ys.length) :
    (storeAll ys pairs)[p]? =
      match lastStored pairs p with
      | some x => some (some x)
      | none => ys[p]? := by
  induction pairs generalizing ys with
  | nil => rfl
  | cons q qs ih =>
    change (storeAll (ys.set (q.1.val - 1).toNat (some q.2)) qs)[p]? = _
    rw [ih _ (fun q h => hpos q (List.mem_cons_of_mem _ h))
      (by rw [List.length_set]; exact hp), batch1_lastStored_cons]
    cases hl : lastStored qs p with
    | some value => rfl
    | none =>
      have hq := hpos q (List.mem_cons_self)
      by_cases hi : q.1.val = (p : Int) + 1
      · rw [if_pos hi, show (q.1.val - 1).toNat = p by omega]
        exact List.getElem?_set_self hp
      · rw [if_neg hi]
        exact List.getElem?_set_ne (by omega)

theorem batch1_mutableShapeCheck_run {s : MutableMemory α} {x mem : Nat}
    {off n : I} {slots : List (Option α)} (v : VecAt s x mem off n slots) (k : I) :
    (mutableShapeCheck x k).run s =
      (if n ≠ k then .error (.dimensionMismatch
        ("tried to assign " ++ toString n.val ++ " elements to " ++
          toString k.val ++ " destinations")) else .ok (), s) := by
  simp only [mutableShapeCheck, stateExcept_bind, mutableLength_run s x _ v.1]
  split <;> rfl

/-- Preflight bounds checks leave the entire memory state unchanged. -/
theorem batch1_vectorBounds_run {s : MutableMemory α} {a mem : Nat}
    {off n : I} {slots : List (Option α)} (v : VecAt s a mem off n slots)
    (idx : List I) :
    (idx.forM (fun i => mutableBounds a i)).run s =
      (if ∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ n.val then .ok () else .error .bounds, s) := by
  simp only [List.forM_eq_forM]
  induction idx with
  | nil => simp only [List.forM_nil, stateExcept_pure, List.not_mem_nil, false_implies,
      implies_true, ite_true]
  | cons i idx ih =>
    rw [List.forM_cons, stateExcept_bind, opusGrowth.vwBounds_run s a mem off n slots v i]
    by_cases hi : 1 ≤ i.val ∧ i.val ≤ n.val
    · rw [if_pos hi]
      simpa only [List.forall_mem_cons, hi, true_and] using ih
    · rw [if_neg hi]
      simp only [List.forall_mem_cons, hi, false_and, ite_false]

theorem batch1_forIn_yield_foldlM {m : Type → Type} [Monad m] [LawfulMonad m]
    (xs : List α) (f : β → α → m β) (start : β) :
    forIn xs start (fun x acc => do pure (.yield (← f acc x))) = xs.foldlM f start := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, List.foldlM_cons, bind_assoc, pure_bind]
    congr 1
    funext next
    exact ih next

def batch1_assignmentKeys (n : Nat) : List I :=
  (List.range n).map (fun k : Nat => JInt.wrap .i64 ((k : Int) + 1))

theorem batch1_assignmentKeys_succ (k : Nat) :
    batch1_assignmentKeys (k + 1) =
      batch1_assignmentKeys k ++ [JInt.wrap .i64 ((k : Int) + 1)] := by
  simp only [batch1_assignmentKeys, List.range_succ, List.map_append,
    List.map_cons, List.map_nil]

theorem batch1_assignmentKeys_intRange (n : I) :
    intRange one n = batch1_assignmentKeys n.val.toNat := by
  simp only [intRange, batch1_assignmentKeys, ival_one,
    show n.val - 1 + 1 = n.val from by omega]
  congr 1
  funext k
  congr 1
  omega

def batch1_assignmentAction (already : α → Bool) (convert : α → Except Error α)
    (a x : Nat) (idx : List I) (k j : I) : MutationM α I := do
  let index ← stateExceptLift (vectorGet idx k)
  let old ← mutableGet x j
  let value ← stateExceptLift (storedValue already convert old)
  mutableSet a value index
  pure (k + one)

theorem batch1_vectorGet_at (idx : List I) (k : Nat)
    (hk : k < idx.length) (hn : idx.length < 2 ^ 62) :
    vectorGet idx (JInt.wrap .i64 ((k : Int) + 1)) = .ok idx[k] := by
  have hv : (JInt.wrap .i64 ((k : Int) + 1)).val = k + 1 := ival_wrap _ (by omega)
  have hb : 1 ≤ (JInt.wrap .i64 ((k : Int) + 1)).val ∧
      (JInt.wrap .i64 ((k : Int) + 1)).val ≤ idx.length := by rw [hv]; omega
  rw [vectorGet, if_pos hb, hv,
    show ((k : Int) + 1 - 1).toNat = k from by omega, List.getElem?_eq_getElem hk]

theorem batch1_vecAt_lengthInt {s : MutableMemory α} {a mem : Nat} {off n : I}
    {slots : List (Option α)} (v : VecAt s a mem off n slots) :
    n.val = (s.contents a).length := by
  have hl := vwWindow_length v
  rw [← v.contents] at hl
  have hn := v.2.2.2.1
  omega

theorem batch1_natIndex_val (k : Nat) (hk : k < 2 ^ 62) :
    (JInt.wrap .i64 ((k : Int) + 1)).val = k + 1 := ival_wrap _ (by omega)

theorem batch1_natSuccBounds (k n : Nat) (hk : k < n) :
    1 ≤ (k : Int) + 1 ∧ (k : Int) + 1 ≤ (n : Int) := by omega

theorem batch1_natIndex_zeroBased (k : Nat) : ((k : Int) + 1 - 1).toNat = k := by
  rw [Int.add_sub_cancel]
  rfl

theorem batch1_natIndex_succ (k : Nat) (hk : k < 2 ^ 62) :
    JInt.wrap .i64 ((k : Int) + 1) + one =
      JInt.wrap .i64 (((k + 1 : Nat) : Int) + 1) := by
  have hj := batch1_natIndex_val k hk
  apply Subtype.ext
  rw [ival_add _ _ (by rw [hj, ival_one]; omega), hj, ival_one,
    ival_wrap _ (by omega)]
  omega

theorem batch1_assignmentAction_success (s : MutableMemory α) (a x ma mx : Nat)
    (oa na ox nx : I) (sa sx : List (Option α))
    (va : VecAt s a ma oa na sa) (vx : VecAt s x mx ox nx sx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (k : Nat) (hki : k < idx.length) (hn : idx.length < 2 ^ 62)
    (hb : 1 ≤ idx[k].val ∧ idx[k].val ≤ na.val) (old value : α)
    (hslot : (s.contents x)[k]? = some (some old))
    (hconv : storedValue already convert old = .ok value) :
    ∃ next slots',
      (batch1_assignmentAction already convert a x idx
        (JInt.wrap .i64 ((k : Int) + 1))
        (JInt.wrap .i64 ((k : Int) + 1))).run s =
        (.ok (JInt.wrap .i64 (((k + 1 : Nat) : Int) + 1)), next) ∧
      batch1_arrayFrame s next ma ∧ VecAt next a ma oa na slots' ∧
      next.contents a = (s.contents a).set (idx[k].val - 1).toNat (some value) := by
  have hkx : k < (s.contents x).length := (List.getElem?_eq_some_iff.mp hslot).choose
  have hj := batch1_natIndex_val k (Nat.lt_trans hki hn)
  have hindex := batch1_vectorGet_at idx k hki hn
  have hnx := batch1_vecAt_lengthInt vx
  have hget := vwGet_run s x mx ox nx sx vx
    (JInt.wrap .i64 ((k : Int) + 1))
    (by rw [hj, hnx]; exact batch1_natSuccBounds k _ hkx)
  rw [← vx.contents, hj, batch1_natIndex_zeroBased k, hslot] at hget
  obtain ⟨next, slots', hset, hf, va', hc⟩ := batch1_arrayStore va idx[k] value hb
  have hnext := batch1_natIndex_succ k (Nat.lt_trans hki hn)
  refine ⟨next, slots', ?_, hf, va', hc⟩
  simp only [batch1_assignmentAction, stateExcept_bind, stateExceptLift_run,
    hindex, hget, hconv, hset, stateExcept_pure, hnext]

theorem batch1_foldlM_extend {σ β γ : Type} (f : β → γ → ExceptT Error (StateM σ) β)
    (xs : List γ) (z k q : β) (j : γ) (s mid next : σ)
    (hr : (xs.foldlM f z).run s = (.ok k, mid))
    (hs : (f k j).run mid = (.ok q, next)) :
    ((xs ++ [j]).foldlM f z).run s = (.ok q, next) := by
  rw [List.foldlM_append, stateExcept_bind, hr]
  simp only [List.foldlM_cons, List.foldlM_nil, stateExcept_bind, hs, stateExcept_pure]

/-- Every converted prefix performs exactly its prefix of indexed writes. -/
theorem batch1_assignmentPrefix (s : MutableMemory α) (a x ma mx : Nat)
    (oa na ox nx : I) (sa sx : List (Option α))
    (va : VecAt s a ma oa na sa) (vx : VecAt s x mx ox nx sx) (hm : ma ≠ mx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (hl : (s.contents x).length = idx.length) (hn : idx.length < 2 ^ 62)
    (hb : ∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ na.val)
    (k : Nat) (hk : k ≤ (s.contents x).length) (cs : List α)
    (hc : ((s.contents x).take k).mapM (storedSlot already convert) = .ok cs) :
    ∃ next slots',
      ((batch1_assignmentKeys k).foldlM
        (batch1_assignmentAction already convert a x idx) one).run s =
        (.ok (JInt.wrap .i64 ((k : Int) + 1)), next) ∧
      batch1_arrayFrame s next ma ∧ VecAt next a ma oa na slots' ∧
      next.contents a = storeAll (s.contents a) ((idx.take k).zip cs) := by
  induction k generalizing cs with
  | zero =>
    change Except.ok [] = Except.ok cs at hc
    cases hc
    exact ⟨s, sa, rfl, batch1_arrayFrame_refl _ _, va, rfl⟩
  | succ k ih =>
    have hkx : k < (s.contents x).length := by omega
    have hki : k < idx.length := by omega
    rw [List.take_succ_eq_append_getElem hkx, List.mapM_append] at hc
    cases hpre : ((s.contents x).take k).mapM (storedSlot already convert) with
    | error e =>
      simp only [hpre, Bind.bind, Except.bind] at hc
      cases hc
    | ok convertedPre =>
      cases hv : storedSlot already convert (s.contents x)[k] with
      | error e =>
        simp only [hpre, List.mapM_cons, List.mapM_nil, hv, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at hc
        cases hc
      | ok value =>
        simp only [hpre, List.mapM_cons, List.mapM_nil, hv, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at hc
        cases hc
        obtain ⟨mid, slots, hrun, hframe, vma, hcontents⟩ :=
          ih (by omega) convertedPre hpre
        have vmx := batch1_arrayFrame_vecAt hframe vx hm
        have hsource : mid.contents x = s.contents x := by rw [vmx.contents, vx.contents]
        cases ho : (s.contents x)[k] with
        | none =>
          simp only [ho, storedSlot] at hv
          cases hv
        | some old =>
          have hconv : storedValue already convert old = .ok value := by
            simpa only [ho, storedSlot] using hv
          have hslot : (mid.contents x)[k]? = some (some old) := by
            rw [hsource, List.getElem?_eq_getElem hkx, ho]
          obtain ⟨next, slots', hstep, hframe', va', hcontents'⟩ :=
            batch1_assignmentAction_success mid a x ma mx oa na ox nx slots sx vma vmx
              idx already convert k hki hn (hb idx[k] (List.getElem_mem hki)) old value hslot hconv
          refine ⟨next, slots', ?_, batch1_arrayFrame_trans hframe hframe', va', ?_⟩
          · rw [batch1_assignmentKeys_succ]
            exact batch1_foldlM_extend _ _ _ _ _ _ _ _ _ hrun hstep
          · rw [hcontents', hcontents, List.take_succ_eq_append_getElem hki]
            have hplen := converted_length (storedSlot already convert)
              ((s.contents x).take k) convertedPre hpre
            have hz : (idx.take k).length = convertedPre.length := by
              simp only [List.length_take] at hplen ⊢
              omega
            rw [List.zip_append hz]
            simp only [List.zip_cons_cons, List.zip_nil_left, storeAll,
              List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem batch1_vectorSetindex_eq (already : α → Bool) (convert : α → Except Error α)
    (a x : Nat) (idx : List I) :
    mutableVectorSetindex already convert a x idx =
      (do mutableShapeCheck x (JInt.wrap .i64 (idx.length : Int))
          idx.forM (fun i => mutableBounds a i)
          let n ← mutableLength x
          let _ ← (intRange one n).foldlM (batch1_assignmentAction already convert a x idx) one
          pure a) := by
  unfold mutableVectorSetindex setindexVector
  simp only [pure_bind, bind_assoc, solArrayGrow.convertingSet_eq]
  have hbody : (fun (j k : I) => do
        let index ← stateExceptLift (vectorGet idx k)
        let old ← mutableGet x j
        let value ← stateExceptLift (storedValue already convert old)
        mutableSet a value index
        pure (ForInStep.yield (k + one))) =
      (fun j k => do pure (.yield (← batch1_assignmentAction already convert a x idx k j))) := by
    funext j k
    simp only [batch1_assignmentAction, bind_assoc, pure_bind]
  rw [hbody]
  simp only [batch1_forIn_yield_foldlM]

theorem batch1_assignmentPreflight (s : MutableMemory α) (a x ma mx : Nat)
    (oa na ox nx : I) (sa sx : List (Option α))
    (va : VecAt s a ma oa na sa) (vx : VecAt s x mx ox nx sx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (hl : (s.contents x).length = idx.length) (hn : idx.length < 2 ^ 62)
    (hb : ∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ na.val) :
    (mutableVectorSetindex already convert a x idx).run s =
      (do let _ ← (batch1_assignmentKeys idx.length).foldlM
            (batch1_assignmentAction already convert a x idx) one
          pure a : MutationM α Nat).run s := by
  have hnx := batch1_vecAt_lengthInt vx
  have heq : nx = JInt.wrap .i64 (idx.length : Int) := by
    apply Subtype.ext
    rw [ival_wrap _ (by omega), hnx, hl]
  have hshape : (mutableShapeCheck x (JInt.wrap .i64 (idx.length : Int))).run s =
      (.ok (), s) := by
    rw [batch1_mutableShapeCheck_run vx, if_neg (by intro h; exact h heq)]
  have hbounds := batch1_vectorBounds_run va idx
  rw [if_pos hb] at hbounds
  rw [batch1_vectorSetindex_eq]
  simp only [stateExcept_bind, hshape, hbounds, mutableLength_run s x _ vx.1,
    batch1_assignmentKeys_intRange, hnx, hl, Int.toNat_natCast]

theorem batch1_assignmentKeys_split (n k : Nat) (hk : k < n) :
    ∃ tail, batch1_assignmentKeys n = batch1_assignmentKeys k ++
      JInt.wrap .i64 ((k : Int) + 1) :: tail := by
  have hlen : (batch1_assignmentKeys n).length = n := by
    simp only [batch1_assignmentKeys, List.length_map, List.length_range]
  have htake : (batch1_assignmentKeys n).take k = batch1_assignmentKeys k := by
    simp only [batch1_assignmentKeys, ← List.map_take, List.take_range,
      Nat.min_eq_left (Nat.le_of_lt hk)]
  have hat : (batch1_assignmentKeys n)[k]'(by omega) = JInt.wrap .i64 ((k : Int) + 1) := by
    simp only [batch1_assignmentKeys, List.getElem_map, List.getElem_range]
  refine ⟨(batch1_assignmentKeys n).drop (k + 1), ?_⟩
  calc
    batch1_assignmentKeys n = (batch1_assignmentKeys n).take k ++
        (batch1_assignmentKeys n).drop k := (List.take_append_drop _ _).symm
    _ = _ := by rw [htake, List.drop_eq_getElem_cons (by omega), hat]

theorem batch1_assignmentAction_error (s : MutableMemory α) (a x mx : Nat)
    (ox nx : I) (sx : List (Option α)) (vx : VecAt s x mx ox nx sx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (k : Nat) (hkx : k < (s.contents x).length) (hki : k < idx.length)
    (hn : idx.length < 2 ^ 62) (e : Error)
    (he : (s.contents x)[k]?.map (storedSlot already convert) = some (.error e)) :
    (batch1_assignmentAction already convert a x idx
      (JInt.wrap .i64 ((k : Int) + 1)) (JInt.wrap .i64 ((k : Int) + 1))).run s =
      (.error e, s) := by
  have hj : (JInt.wrap .i64 ((k : Int) + 1)).val = k + 1 := ival_wrap _ (by omega)
  have hindex := batch1_vectorGet_at idx k hki hn
  have hnx := batch1_vecAt_lengthInt vx
  have hget := vwGet_run s x mx ox nx sx vx
    (JInt.wrap .i64 ((k : Int) + 1)) (by rw [hj, hnx]; omega)
  rw [← vx.contents, hj, show ((k : Int) + 1 - 1).toNat = k from by omega,
    List.getElem?_eq_getElem hkx] at hget
  simp only [List.getElem?_eq_getElem hkx, Option.map_some] at he
  cases ho : (s.contents x)[k] with
  | none =>
    rw [ho] at hget
    simp only [ho, storedSlot, Option.some.injEq, Except.error.injEq] at he
    rw [← he]
    simp only [batch1_assignmentAction, stateExcept_bind, stateExceptLift_run, hindex, hget]
  | some old =>
    rw [ho] at hget
    have hconv : storedValue already convert old = .error e := by
      simpa only [ho, storedSlot, Option.some.injEq] using he
    simp only [batch1_assignmentAction, stateExcept_bind, stateExceptLift_run,
      hindex, hget, hconv]

theorem batch1_natLength_val (n : Nat) (hn : n < 2 ^ 62) :
    (JInt.wrap .i64 (n : Int)).val = n := ival_wrap _ (by omega)

theorem batch1_assignmentDimMismatch (s : MutableMemory α) (a x mx : Nat)
    (ox nx : I) (sx : List (Option α)) (vx : VecAt s x mx ox nx sx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (hn : idx.length < 2 ^ 62) (hlength : ((s.contents x).length : Int) ≠ idx.length) :
    ∃ message, (mutableVectorSetindex already convert a x idx).run s =
      (.error (.dimensionMismatch message), s) := by
  have hnx := batch1_vecAt_lengthInt vx
  have hiv := batch1_natLength_val idx.length hn
  have hne : nx ≠ JInt.wrap .i64 (idx.length : Int) := by
    intro he
    have he' := congrArg Subtype.val he
    rw [hnx, hiv] at he'
    exact hlength he'
  refine ⟨"tried to assign " ++ toString nx.val ++ " elements to " ++
    toString (JInt.wrap .i64 (idx.length : Int)).val ++ " destinations", ?_⟩
  rw [batch1_vectorSetindex_eq, stateExcept_bind, batch1_mutableShapeCheck_run vx,
    if_pos hne]

theorem batch1_assignmentOutOfBounds (s : MutableMemory α) (a x ma mx : Nat)
    (oa na ox nx : I) (sa sx : List (Option α))
    (va : VecAt s a ma oa na sa) (vx : VecAt s x mx ox nx sx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (hn : idx.length < 2 ^ 62) (hlength : (s.contents x).length = idx.length)
    (hbad : ∃ i ∈ idx, ¬ (1 ≤ i.val ∧ i.val ≤ na.val)) :
    (mutableVectorSetindex already convert a x idx).run s = (.error .bounds, s) := by
  have hnx := batch1_vecAt_lengthInt vx
  have hiv := batch1_natLength_val idx.length hn
  have heq : nx = JInt.wrap .i64 (idx.length : Int) := by
    apply Subtype.ext
    rw [hnx, hiv, hlength]
  have hshape : (mutableShapeCheck x (JInt.wrap .i64 (idx.length : Int))).run s =
      (.ok (), s) := by
    rw [batch1_mutableShapeCheck_run vx, if_neg (by intro h; exact h heq)]
  have hfalse : ¬ (∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ na.val) := by
    intro hall
    obtain ⟨i, hi, hbad⟩ := hbad
    exact hbad (hall i hi)
  have hbounds := batch1_vectorBounds_run va idx
  rw [if_neg hfalse] at hbounds
  rw [batch1_vectorSetindex_eq]
  simp only [stateExcept_bind, hshape, hbounds]

theorem batch1_foldlM_error_after {σ β γ : Type} (f : β → γ → ExceptT Error (StateM σ) β)
    (xs tail : List γ) (z k : β) (j : γ) (s mid : σ) (e : Error)
    (hr : (xs.foldlM f z).run s = (.ok k, mid))
    (hs : (f k j).run mid = (.error e, mid)) :
    ((xs ++ j :: tail).foldlM f z).run s = (.error e, mid) := by
  rw [List.foldlM_append, stateExcept_bind, hr]
  simp only [List.foldlM_cons, stateExcept_bind, hs]

theorem batch1_stateExcept_then_error {σ β γ : Type}
    (action : ExceptT Error (StateM σ) β) (s next : σ) (e : Error) (a : γ)
    (h : action.run s = (.error e, next)) :
    (do let _ ← action; pure a : ExceptT Error (StateM σ) γ).run s = (.error e, next) := by
  rw [stateExcept_bind, h]

theorem batch1_assignmentFailure (s : MutableMemory α) (a x ma mx : Nat)
    (oa na ox nx : I) (sa sx : List (Option α))
    (va : VecAt s a ma oa na sa) (vx : VecAt s x mx ox nx sx) (hm : ma ≠ mx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (hlength : (s.contents x).length = idx.length) (hn : idx.length < 2 ^ 62)
    (hb : ∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ na.val)
    (k : Nat) (cs : List α) (e : Error)
    (hc : ((s.contents x).take k).mapM (storedSlot already convert) = .ok cs)
    (he : (s.contents x)[k]?.map (storedSlot already convert) = some (.error e)) :
    ∃ next, (mutableVectorSetindex already convert a x idx).run s = (.error e, next) ∧
      batch1_arrayFrame s next ma ∧
      next.contents a = storeAll (s.contents a) ((idx.take k).zip cs) := by
  have hpre := batch1_assignmentPreflight s a x ma mx oa na ox nx sa sx
    va vx idx already convert hlength hn hb
  have hk : k < (s.contents x).length := by
    by_cases hk : k < (s.contents x).length
    · exact hk
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt hk), Option.map_none] at he
      cases he
  obtain ⟨next, slots', hrun, hframe, va', hcontents⟩ :=
    batch1_assignmentPrefix s a x ma mx oa na ox nx sa sx va vx hm idx already convert
      hlength hn hb k (Nat.le_of_lt hk) cs hc
  have vx' := batch1_arrayFrame_vecAt hframe vx hm
  have hsource : next.contents x = s.contents x := by rw [vx'.contents, vx.contents]
  have hstep := batch1_assignmentAction_error next a x mx ox nx sx vx' idx already convert
    k (by rw [hsource]; exact hk) (by rw [← hlength]; exact hk) hn e (by rw [hsource]; exact he)
  obtain ⟨tail, hsplit⟩ := batch1_assignmentKeys_split idx.length k (by rw [← hlength]; exact hk)
  have hfold : ((batch1_assignmentKeys idx.length).foldlM
      (batch1_assignmentAction already convert a x idx) one).run s = (.error e, next) := by
    rw [hsplit]
    exact batch1_foldlM_error_after _ _ _ _ _ _ _ _ _ hrun hstep
  refine ⟨next, ?_, hframe, hcontents⟩
  exact hpre.trans (batch1_stateExcept_then_error _ s next e a hfold)

theorem batch1_assignmentSuccess (s : MutableMemory α) (a x ma mx : Nat)
    (oa na ox nx : I) (sa sx : List (Option α))
    (va : VecAt s a ma oa na sa) (vx : VecAt s x mx ox nx sx) (hm : ma ≠ mx)
    (idx : List I) (already : α → Bool) (convert : α → Except Error α)
    (hlength : (s.contents x).length = idx.length) (hn : idx.length < 2 ^ 62)
    (hb : ∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ na.val) (cs : List α)
    (hc : (s.contents x).mapM (storedSlot already convert) = .ok cs) :
    ∃ next, (mutableVectorSetindex already convert a x idx).run s = (.ok a, next) ∧
      batch1_arrayFrame s next ma ∧ next.validVector a ∧
      next.contents a = storeAll (s.contents a) (idx.zip cs) := by
  have hpre := batch1_assignmentPreflight s a x ma mx oa na ox nx sa sx
    va vx idx already convert hlength hn hb
  obtain ⟨next, slots', hrun, hframe, va', hcontents⟩ :=
    batch1_assignmentPrefix s a x ma mx oa na ox nx sa sx va vx hm idx already convert
      hlength hn hb idx.length (Nat.le_of_eq hlength.symm) cs
        (by simpa only [← hlength, List.take_length] using hc)
  have hcontents' : next.contents a = storeAll (s.contents a) (idx.zip cs) := by
    simpa only [List.take_length] using hcontents
  refine ⟨next, ?_, hframe, va'.valid, hcontents'⟩
  rw [hpre]
  simp only [stateExcept_bind, hrun, stateExcept_pure]

/-- Indexed assignment checks its whole destination first, then stores converted source slots in order. -/
theorem MultidimcovArrayV2SetindexVector_proven :
    JuliaLean.Proofs.base.array.VectorIndexSetSpec := by
  intro α s a x idx already convert hva hvx hdistinct hn
  obtain ⟨ma, oa, na, sa, va⟩ := validVector_vecAt hva
  obtain ⟨mx, ox, nx, sx, vx⟩ := validVector_vecAt hvx
  have hm : ma ≠ mx := hdistinct _ _ va.1 vx.1
  have hna := batch1_vecAt_lengthInt va
  have hothers : ∀ next : MutableMemory α, batch1_arrayFrame s next ma →
      next.arrays = s.arrays ∧
        ∀ mem, (∀ v, s.arrays[a]? = some v → v.reference.1 ≠ mem) →
          next.memories[mem]? = s.memories[mem]? := by
    intro next hf
    refine ⟨hf.1, ?_⟩
    intro mem hmem
    exact hf.2 mem (hmem _ va.1)
  dsimp only
  refine ⟨batch1_assignmentDimMismatch s a x mx ox nx sx vx idx already convert hn, ?_, ?_⟩
  · intro hlength hbad
    apply batch1_assignmentOutOfBounds s a x ma mx oa na ox nx sa sx va vx
      idx already convert hn hlength
    simpa only [hna] using hbad
  · intro hlength hbounds
    have hb : ∀ i ∈ idx, 1 ≤ i.val ∧ i.val ≤ na.val := by
      simpa only [hna] using hbounds
    refine ⟨?_, ?_⟩
    · intro k cs e hc he
      obtain ⟨next, hrun, hf, hcontents⟩ :=
        batch1_assignmentFailure s a x ma mx oa na ox nx sa sx va vx hm idx already convert
          hlength hn hb k cs e hc he
      exact ⟨next, hrun, hothers next hf, hcontents⟩
    · intro cs hc
      obtain ⟨next, hrun, hf, hva', hcontents⟩ :=
        batch1_assignmentSuccess s a x ma mx oa na ox nx sa sx va vx hm idx already convert
          hlength hn hb cs hc
      refine ⟨next, hrun, hothers next hf, hva', hcontents, ?_⟩
      intro p hp
      rw [hcontents]
      apply batch1_storeAll_get _ _ _ p hp
      intro q hq
      exact (hb q.1 (List.of_mem_zip hq).1).1
end ChatGPTBatch1.ArrayAssignment
end
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2
open JuliaLean JuliaLean.base.array JuliaLean.src.genericmemory_c
open JuliaLean.Proofs.base.array

theorem slotBoundsRun (n : Nat) (i : I) (slots : I → Option α) :
    (slotBounds n () i).run slots =
      (if 1 ≤ i.val ∧ i.val ≤ (n : Int) then .ok () else .error .bounds, slots) := rfl

theorem slotRefRun (i : I) (slots : I → Option α) :
    (slotRef () i).run slots = (.ok i, slots) := rfl

theorem slotRefNewRun (i : I) (b : Bool) (slots : I → Option α) :
    (slotRefNew () i b).run slots = (.ok i, slots) := rfl

theorem slotUnsetPrimitiveRun (runtime : DictLayout) (i : I) (slots : I → Option α) :
    (slotUnset runtime i).run slots =
      (.ok (), updateSlot slots i (unsetCell runtime i.val.toNat (slots i))) := rfl

theorem slotStorePrimitiveRun (i : I) (x : α) (b : Bool) (slots : I → Option α) :
    (slotStore i x b).run slots = (.ok (), updateSlot slots i (some x)) := rfl

theorem slotReadRun (i : I) (slots : I → Option α) :
    (slotRead i).run slots =
      ((match slots i with | some x => .ok x | none => .error .undefinedReference), slots) := rfl

theorem slotLiftRun (value : Except Error α) (slots : I → Option β) :
    (slotLift value).run slots = (value, slots) := rfl

 theorem slotUnsetRun (runtime : DictLayout) (n : Nat) (i : I) (slots : I → Option α) :
    (unsetindexInt (slotBounds n) slotRef (slotUnset runtime) () i).run slots =
      if 1 ≤ i.val ∧ i.val ≤ (n : Int)
      then (.ok (), updateSlot slots i (expectedUnset runtime (slots i)))
      else (.error .bounds, slots) := by
  by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int)
  · simp only [unsetindexInt, stateExcept_bind, slotBoundsRun, if_pos hb, slotRefRun,
      slotUnsetPrimitiveRun, stateExcept_pure, unsetCell_result]
  · simp only [unsetindexInt, stateExcept_bind, slotBoundsRun, if_neg hb]

 theorem slotStoreRun (n : Nat) (i : I) (x : α) (slots : I → Option α) :
    (setindexTyped (slotBounds n) slotRefNew slotStore () x i).run slots =
      if 1 ≤ i.val ∧ i.val ≤ (n : Int)
      then (.ok (), updateSlot slots i (some x)) else (.error .bounds, slots) := by
  by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int)
  · simp only [setindexTyped, stateExcept_bind, slotBoundsRun, if_pos hb, slotRefNewRun,
      slotStorePrimitiveRun, stateExcept_pure]
  · simp only [setindexTyped, stateExcept_bind, slotBoundsRun, if_neg hb]

 theorem slotScalarRun (n : Nat) (i : I) (slots : I → Option α)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α) (v : β) :
    (setindexScalar already asTyped (fun v => slotLift (convert v))
      (setindexTyped (slotBounds n) slotRefNew slotStore) () v i).run slots =
      match (if already v then .ok (asTyped v) else convert v) with
      | .error e => (.error e, slots)
      | .ok y => if 1 ≤ i.val ∧ i.val ≤ (n : Int)
          then (.ok (), updateSlot slots i (some y)) else (.error .bounds, slots) := by
  unfold setindexScalar
  cases h : already v with
  | true =>
    simp only [h, ite_true, pure_bind]
    exact slotStoreRun n i _ slots
  | false =>
    simp only [h, Bool.false_eq_true, ite_false, stateExcept_bind, slotLiftRun]
    cases convert v with
    | error e => rfl
    | ok y => exact slotStoreRun n i y slots

 theorem groupLinearAccess : LinearAccessSpec := by
  intro runtime α β n slots i x already asTyped convert v
  dsimp only
  refine ⟨slotUnsetRun runtime n i slots, slotStoreRun n i x slots, ?_, ?_, ?_, ?_⟩
  · intro hb
    rw [stateExcept_bind, slotStoreRun, if_pos hb]
    simp only [slotReadRun, updateSlot, ite_true]
  · intro e he
    rw [slotScalarRun, he]
  · intro y hy
    rw [slotScalarRun, hy]
  · intro _ j hji
    simp only [updateSlot, if_neg hji, and_self]

 theorem groupReadable : ReadableSpec := by
  intro runtime α slots n i
  refine ⟨?_, ?_, ?_⟩
  · rw [(assignmentSpec α slots n i).1]
    constructor
    · rintro ⟨h1, h2, x, hx⟩
      refine ⟨x, ?_⟩
      simp only [slotGet, stateExcept_bind, slotBoundsRun, show (1 ≤ i.val ∧ i.val ≤ (n : Int)) from ⟨h1,h2⟩,
        and_self, ite_true, slotReadRun, hx]
    · rintro ⟨x, hx⟩
      by_cases hb : 1 ≤ i.val ∧ i.val ≤ (n : Int)
      · refine ⟨hb.1, hb.2, ?_⟩
        simp only [slotGet, stateExcept_bind, slotBoundsRun, if_pos hb, slotReadRun] at hx
        cases hs : slots i with
        | none => simp only [hs] at hx; cases hx
        | some y => exact ⟨y, rfl⟩
      · simp only [slotGet, stateExcept_bind, slotBoundsRun, if_neg hb] at hx
        cases hx
  · intro hb
    simp only [slotGet, stateExcept_bind, slotBoundsRun, if_neg hb]
  · intro hb
    rw [stateExcept_bind, slotUnsetRun, if_pos hb]
    simp only [slotReadRun, updateSlot, ite_true]

 theorem MultidimcovArrayV2LinearAccess_proven : JuliaLean.Proofs.base.array.LinearAccessComplete :=
  ⟨groupLinearAccess, assignmentSpec, groupReadable⟩
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace JuliaLean.ChatGPT.Batch4.Group2

open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array

set_option maxRecDepth 16384

theorem groupCartesianAssignmentRun {α β : Type} (slots : I → Option α)
    (bounds : List I → Bool) (linear : List I → Except Error I)
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
    (v : β) (i₁ i₂ : I) (rest : List I) :
    (setindexCartesian (fun x => if already x then some (asTyped x) else none)
      (fun x => slotLift (convert x)) pure
      (setindexCartesianTyped
        (fun _ js => slotLift (if bounds js then .ok () else .error .bounds))
        (fun _ js => slotLift (linear js)) slotRefNew slotStore) () v i₁ i₂ rest).run slots =
    match (if already v then .ok (asTyped v) else convert v) with
    | .error e => (.error e, slots)
    | .ok x =>
      if bounds (i₁ :: i₂ :: rest) then
        match linear (i₁ :: i₂ :: rest) with
        | .error e => (.error e, slots)
        | .ok i => (.ok (), updateSlot slots i (some x))
      else (.error .bounds, slots) := by
  cases ha : already v <;> cases hc : convert v <;>
    cases hb : bounds (i₁ :: i₂ :: rest) <;>
    cases hl : linear (i₁ :: i₂ :: rest) <;>
    simp only [setindexCartesian, setindexCartesianTyped, ha, hc, hb, hl,
      Bool.false_eq_true, ite_false, ite_true,
      slotLift, slotRefNew, slotStore, ExceptT.run, ExceptT.bind, ExceptT.pure,
      ExceptT.mk, ExceptT.bindCont, StateT.bind, StateT.pure, Bind.bind, Pure.pure] <;> rfl

theorem ArrayCartesianAssignment_proven : JuliaLean.Proofs.base.array.CartesianAssignmentSpec := by
  intro α β slots bounds linear already asTyped convert v i₁ i₂ rest
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    rw [groupCartesianAssignmentRun, he]
  · intro x hx hb
    rw [groupCartesianAssignmentRun, hx, hb] <;> rfl
  · intro x e hx hb he
    rw [groupCartesianAssignmentRun, hx, hb]
    change (match linear (i₁ :: i₂ :: rest) with
      | .error err => ((Except.error err : Except Error Unit), slots)
      | .ok i => (Except.ok (), updateSlot slots i (some x))) = (Except.error e, slots)
    rw [he]
  · intro x i hx hb hi
    refine ⟨?_, ?_, ?_⟩
    · rw [groupCartesianAssignmentRun, hx, hb]
      change (match linear (i₁ :: i₂ :: rest) with
        | .error err => ((Except.error err : Except Error Unit), slots)
        | .ok j => (Except.ok (), updateSlot slots j (some x))) =
          (Except.ok (), updateSlot slots i (some x))
      rw [hi]
    · exact if_pos rfl
    · intro j hj
      exact if_neg hj

theorem ArrayRangeIndexOrdinary_proven : JuliaLean.Proofs.base.array.OrdinaryRangeIndexSpec := by
  intro R α values get getBool h r i
  constructor
  · change (get r i).map Except.ok = _
    rw [h r i]
    cases he : (values r)[(i.val - 1).toNat]? with
    | none => rfl
    | some value =>
      dsimp only
      by_cases hi : 1 ≤ i.val <;>
        simp only [hi, ite_true, ite_false, Except.map]
  · intro b
    rfl

theorem MultidimcovRangeGetindexUnsigned_refuted :
    ¬ JuliaLean.Proofs.base.array.ScalarRangeIndexSpec := by
  intro h
  have bad := h.2.2.1 .i8 .u8
    (⟨JInt.wrap .i8 (-2), JInt.wrap .i8 2⟩ : JuliaLean.base.range.UnitRange (JInt .i8))
    (JInt.wrap .u8 1) (by decide)
  change (Except.error (.jl .boundsError) :
    JuliaLean.base.range.JlX (Except Error (JInt .i8))) =
      .ok (.ok (JInt.wrap .i8 (-2))) at bad
  cases bad
end JuliaLean.ChatGPT.Batch4.Group2
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
section

/- Integer unsetting partials -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
namespace JuliaLean.ChatGPT.Batch5.Group3
open JuliaLean JuliaLean.base.array JuliaLean.Proofs.base.array
open JuliaLean.src.genericmemory_c

/-- Every non-Boolean integer fitting Int is converted to its equal Int by the frozen call. -/
theorem arrayIndexFits (ops : round4.BigIntegerOps) (hops : ops.Lawful)
    (i : round4.IntegerValue) (hbool : i.isBool = false) (hfit : i.fits) :
    round4.arrayToIndex ops i = .ok (JInt.wrap .i64 i.val) := by
  cases i with
  | bool b => cases hbool
  | big v =>
    change IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max at hfit
    simp only [round4.arrayToIndex, JuliaLean.base.indices.to_index_Integer, hops.1,
      if_pos hfit, Except.mapError, bind, Except.bind, pure, Except.pure,
      round4.IntegerValue.val]
  | bit t x =>
    change IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max at hfit
    cases t <;>
      simp [round4.arrayToIndex, JuliaLean.base.indices.to_index_Array,
        JuliaLean.base.indices.to_index_A_i, JuliaLean.base.indices.to_index,
        JuliaLean.base.indices.to_index_Integer, JuliaLean.base.indices.convert_Int_BitInteger,
        JuliaLean.base.int.convert, JInt.convert, round4.IntegerValue.val,
        hfit, Except.mapError]
    all_goals apply Subtype.ext
    all_goals first
      | exact (ival_wrap _ hfit).symm
      | exact JuliaLean.Proofs.base.int.bitcast_val .i64 x rfl

/-- For a representable non-Boolean index, failure of bounds leaves the complete store unchanged. -/
theorem unsetIntegerBounds {α : Type} (runtime : DictLayout)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α) (a : Nat)
    (i : round4.IntegerValue) (hvalid : s.validVector a)
    (hbool : i.isBool = false) (hfit : i.fits)
    (hbad : ¬ (1 ≤ i.val ∧ i.val ≤ ((s.contents a).length : Int))) :
    (unsetindexInteger (fun i => round4.stateExceptLift (round4.arrayToIndex ops i))
      (fun a i => do mutableUnset runtime a i; pure a) a i).run s = (.error .bounds, s) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvalid
  have hn0 := hv.2.2.2.1
  have hlen : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv]
    omega
  have hconvert := arrayIndexFits ops hops i hbool hfit
  have hvalue : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hfit
  have hnot : ¬ (one ≤ JInt.wrap .i64 i.val ∧ JInt.wrap .i64 i.val ≤ n) := by
    simpa only [jle_iff, ival_one, hvalue, hlen] using hbad
  simp only [unsetindexInteger, stateExcept_bind, integerLiftRun, hconvert,
    mutableUnset, unsetindexInt, mutableBounds, mutableInBounds, mutableLength,
    mutableVector_run, hv.1, stateExcept_pure, hnot, decide_false, Bool.not_false,
    ite_true, stateExcept_throw]

/-- The successful branch of the frozen unsetting contract, including raw memory and headers. -/
theorem unsetIntegerSuccess {α : Type} (runtime : DictLayout)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α) (a : Nat)
    (i : round4.IntegerValue) (hvalid : s.validVector a)
    (hi : i.validIndex (s.contents a).length) :
    ∃ next,
      (unsetindexInteger (fun i => round4.stateExceptLift (round4.arrayToIndex ops i))
        (fun a i => do mutableUnset runtime a i; pure a) a i).run s = (.ok a, next) ∧
      next.arrays = s.arrays ∧ next.validVector a ∧
      next.contents a = (s.contents a).set (i.val - 1).toNat
        (expectedUnset runtime ((s.contents a)[(i.val - 1).toNat]?).join) ∧
      (∀ vector rawSlots, s.arrays[a]? = some vector →
        s.memories[vector.reference.1]? = some rawSlots →
        let address := (vector.reference.2.val + i.val - 2).toNat
        next.memories = s.memories.set vector.reference.1
          (rawSlots.set address (expectedUnset runtime (rawSlots[address]?).join))) := by
  obtain ⟨mem, off, n, slots, hv⟩ := validVector_vecAt hvalid
  have hoff := hv.2.2.1
  have hn0 := hv.2.2.2.1
  have hlen : ((s.contents a).length : Int) = n.val := by
    rw [hv.contents, vwWindow_length hv]
    omega
  have hin : 1 ≤ i.val ∧ i.val ≤ n.val := by
    simpa only [hlen] using hi.2
  have hfit : i.fits := by
    have hn := ival_bounds n
    change -9223372036854775808 ≤ i.val ∧ i.val ≤ 9223372036854775807
    omega
  have hconvert := arrayIndexFits ops hops i hi.1 hfit
  have hvalue : (JInt.wrap .i64 i.val).val = i.val := ival_wrap _ hfit
  let address := (off.val - 1 + i.val - 1).toNat
  let value := expectedUnset runtime (slots[address]?).join
  let next : MutableMemory α :=
    { s with memories := s.memories.set mem (slots.set address value) }
  have hvnext : VecAt next a mem off n (slots.set address value) := hv.set address value
  have hstep := vwMutableUnset_run (unsetRuntime := runtime) s a mem off n slots hv
    (JInt.wrap .i64 i.val) (by simpa only [hvalue] using hin)
  simp only [hvalue] at hstep
  have hslot : ((s.contents a)[(i.val - 1).toNat]?).join = (slots[address]?).join := by
    rw [hv.contents, vwWindow_get hv]
    rw [if_pos (by omega)]
    congr 2
    dsimp only [address]
    omega
  refine ⟨next, ?_, rfl, hvnext.valid, ?_, ?_⟩
  · simp only [unsetindexInteger, stateExcept_bind, integerLiftRun, hconvert,
      hstep, stateExcept_pure]
    rfl
  · have hw := vwWindow_set slots off n (JInt.wrap .i64 i.val) value hoff
      (by simpa only [hvalue] using hin.1)
    simp only [hvalue] at hw
    change vwWindow (slots.set address value) off n =
      (vwWindow slots off n).set (i.val - 1).toNat value at hw
    rw [hvnext.contents, hw, ← hv.contents, hslot]
  · intro vector rawSlots hvector hslots
    rw [hv.1] at hvector
    cases hvector
    rw [hv.2.1] at hslots
    cases hslots
    dsimp only [next, address, value]
    rw [show off.val - 1 + i.val - 1 = off.val + i.val - 2 by omega]

/-- The inexact branch holds for every non-Boolean input except the special UInt64 dispatch. -/
theorem unsetIntegerInexactExceptUInt {α : Type} (runtime : DictLayout)
    (ops : round4.BigIntegerOps) (hops : ops.Lawful) (s : MutableMemory α) (a : Nat)
    (i : round4.IntegerValue) (hbool : i.isBool = false)
    (huint : i.isBit .u64 = false) (hfit : ¬ i.fits) :
    (unsetindexInteger (fun i => round4.stateExceptLift (round4.arrayToIndex ops i))
      (fun a i => do mutableUnset runtime a i; pure a) a i).run s = (.error .inexact, s) := by
  apply unsetIntegerConversionError
  cases i with
  | bool b => cases hbool
  | big v =>
    change ¬ (IntTy.i64.min ≤ v ∧ v ≤ IntTy.i64.max) at hfit
    simp only [round4.arrayToIndex, JuliaLean.base.indices.to_index_Integer, hops.1,
      if_neg hfit, Except.mapError, bind, Except.bind, pure, Except.pure, round4.indexError]
  | bit t x =>
    change ¬ (IntTy.i64.min ≤ x.val ∧ x.val ≤ IntTy.i64.max) at hfit
    cases t <;>
      simp [round4.IntegerValue.isBit] at huint
    all_goals simp [round4.arrayToIndex, JuliaLean.base.indices.to_index_Array,
      JuliaLean.base.indices.to_index_A_i, JuliaLean.base.indices.to_index,
      JuliaLean.base.indices.to_index_Integer, JuliaLean.base.indices.convert_Int_BitInteger,
      JuliaLean.base.int.convert, JInt.convert, hfit, Except.mapError, round4.indexError]
end JuliaLean.ChatGPT.Batch5.Group3
end


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion2
open JuliaLean JuliaLean.base.array
open JuliaLean.base.array.Completion2

/-- Taking an array makes the destination reference and size alias the source, returns the destination, and preserves every other header. -/
def TakeAliasesAndFrame : Prop :=
  ∀ (Ref Dims : Type) [DecidableEq Ref] [DecidableEq Dims]
    (headers : Nat → Ref × Dims) (dst src : Nat),
    let result := (takeFields (Ref := Ref) (Dims := Dims) dst src).run headers
    result.1 = dst ∧ result.2 dst = headers src ∧
      (∀ a, a ≠ dst → result.2 a = headers a)

/-- Safe indexing preserves every original read argument without recursively rewriting it, and rejects an assignment expression with no left-hand argument. -/
def RawSafeindexReadAndBounds : Prop :=
  ∀ (Atom : Type) (args : List (RawExpr Atom)),
    safeindexRaw (.expr "ref" args) =
      .ok (.expr "call" (.globalRef "__safe_getindex" :: args)) ∧
    safeindexRaw (Atom := Atom) (.expr "=" []) = .error .bounds

/-- The macro wraps every successful expansion in exactly one escape expression and propagates malformed-assignment errors. -/
def SafeindexMacroEscape : Prop :=
  ∀ (Atom : Type) (e : RawExpr Atom),
    (∀ expanded, safeindexMacro e = .ok expanded →
      ∃ rewritten, expanded = .expr "escape" [rewritten]) ∧
    safeindexMacro (Atom := Atom) (.expr "=" []) = .error .bounds
end JuliaLean.Proofs.base.array.Completion2


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion3
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion3

/-- Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable. -/
def UnsetIntegerConversionFailures : Prop :=
  ∀ (State T V D N Mod P Sym Ref Z : Type)
    (layout : LayoutBoundary (NativeGrowthWorld State T) V D N Mod P Sym Ref)
    (elementType : V) (native : NativeCopyOps (NativeGrowthState State T) T)
    (ccall : NativeMemmove) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (toInt : Z → NativeGrowthM State T I) (a : Nat) (delta : Z) (before : NativeGrowthWorld State T),
    FirstNativeFailure (toInt delta)
      (JuliaLean.base.array.Completion3.unsetInteger layout elementType native ccall allocation access references
        toInt a delta) before

/-- The safe converting setter propagates conversion failures and divergence before reading a vector reference or storing a value. -/
def SafeSetindexConversionFailures : Prop :=
  ∀ (State T X : Type) (access : NativeGrowthAccess State T)
    (references : NativeGrowthReferenceOps State T)
    (convert : X → NativeGrowthM State T X) (cast : X → Option T)
    (a : Nat) (x : X) (i : I) (before : NativeGrowthWorld State T),
    FirstNativeFailure (convert x)
      (JuliaLean.base.array.Completion3.safeSetindexConvert access references convert cast a x i) before
end JuliaLean.Proofs.base.array.Completion3


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion4
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.base.array.Completion4
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- Bool-range index conversion happens before indexing the array, retaining conversion errors and their effects. -/
def BooleanRangeIndexConversionErrors : Prop :=
  ∀ (W A R Indices B : Type) (toIndex : R → ExceptT Error (StateM W) Indices)
    (get : A → Indices → ExceptT Error (StateM W) B)
    (a : A) (r : R) (before after : W) (error : Error),
    (toIndex r).run before = (.error error, after) →
    (JuliaLean.base.array.Completion4.getindexBoolRange toIndex get a r).run before = (.error error, after)

/-- Unit-range slicing checks bounds before length, axes, allocation or copying, retaining the exact error and world from the check. -/
def UnitRangeBoundsErrors : Prop :=
  ∀ (W A R Count Axes B DestIndex SrcIndex C : Type)
    (bounds : A → R → ExceptT Error (StateM W) Unit)
    (length : R → ExceptT Error (StateM W) Count) (axes : R → ExceptT Error (StateM W) Axes)
    (similar : A → Axes → ExceptT Error (StateM W) B)
    (positive : Count → ExceptT Error (StateM W) (Option Bool))
    (firstindex : B → ExceptT Error (StateM W) DestIndex) (first : R → ExceptT Error (StateM W) SrcIndex)
    (copy : B → DestIndex → A → SrcIndex → Count → ExceptT Error (StateM W) C)
    (a : A) (r : R) (before after : W) (error : Error),
    (bounds a r).run before = (.error error, after) →
    (JuliaLean.base.array.Completion4.getindexUnitRange bounds length axes similar positive firstindex first
      copy a r).run before = (.error error, after)

/-- Contiguous assignment checks destination bounds before length, shape compatibility or copying, retaining errors and preceding effects. -/
def UnitRangeAssignmentBoundsErrors : Prop :=
  ∀ (W A R Count Start C : Type) (bounds : A → R → ExceptT Error (StateM W) Unit)
    (length : R → ExceptT Error (StateM W) Count) (shape : A → Count → ExceptT Error (StateM W) Unit)
    (positive : Count → ExceptT Error (StateM W) (Option Bool)) (first : R → ExceptT Error (StateM W) Start)
    (copy : A → Start → A → I → Count → ExceptT Error (StateM W) C)
    (a x : A) (r : R) (before after : W) (error : Error),
    (bounds a r).run before = (.error error, after) →
    (JuliaLean.base.array.Completion4.setindexUnitRange bounds length shape positive first copy a x r).run before =
      (.error error, after)

/-- Every-rank scalar assignment converts and type-asserts the value before reading live dimensions, checking bounds or invoking native reference/store primitives. -/
def ScalarArrayConversionFailures : Prop :=
  ∀ (State T X : Type) (native : NativeFillBoundary (NativeLiveState State T) T)
    (cast : X → Option T) (convert : X → NativeLiveM State T X)
    (rank a : Nat) (x : X) (i : I) (before : NativeLiveWorld State T),
    cast x = none →
    FirstNativeFailure (convert x)
      (JuliaLean.base.array.Completion4.setindexScalar native cast convert rank a x i) before
end JuliaLean.Proofs.base.array.Completion4


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Completion6
open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
open JuliaLean.Proofs.base.array.Completion3 (FirstNativeFailure)

/-- A typed literal allocates before observing or converting any element.
All native allocation errors, partial states and divergence remain observable. -/
def TypedLiteralAllocationFailures : Prop :=
  ∀ (State T E : Type) (allocation : NativeAllocationBoundary (NativeGrowthState State T) T)
    (access : NativeGrowthAccess State T) (references : NativeGrowthReferenceOps State T)
    (cast : E → Option T) (convert : E → NativeGrowthM State T E)
    (homogeneous : Bool) (values : TupleArgs E) (before : NativeGrowthWorld State T),
    FirstNativeFailure (nativeVectorUndef allocation (JInt.wrap .i64 values.values.length))
      (JuliaLean.base.array.Completion6.typedLiteral allocation access references cast convert homogeneous values) before
end JuliaLean.Proofs.base.array.Completion6


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Mathematical cardinality of a native Array header. This is specification
arithmetic, not the machine-arithmetic length implementation. Julia source:
base/array.jl:323,330-332; essentials.jl:12-14,1296. -/
def CopyArrayCount (a : CopyArrayHeader) : Nat :=
  (a.dimensions.map (fun d => d.val.toNat)).prod

/-- Necessary native size/window invariants for a Memory projection in the existing
cell runtime. They are not a complete physical byte/address certificate. The zero-length case permits a one-past-end offset. The common native length
envelope comes from src/genericmemory.c:161 (unsafe_wrap). Julia source:
base/array.jl:299-315,331-332 (native Array/Memory objects and their references). -/
def CopyMemoryValid {α : Type} (state : MutableMemory α) (m : CopyMemoryWindow) : Prop :=
  ∃ cells : List (Option α), state.memories[m.backing]? = some cells ∧
    cells.length < 2 ^ 63 - 1 ∧ 0 ≤ m.length.val ∧ 1 ≤ m.offset.val ∧
    m.offset.val - 1 + m.length.val ≤ (cells.length : Int)

/-- Necessary native size-tuple and reference-window invariants. Rank zero has
cardinality one; every dimension may be zero and every rank is admitted within
the native tuple-length bound. No correctness law about copy or length is assumed.
Julia source: base/array.jl:323,330-332; essentials.jl:12-14,1296. -/
def CopyArrayValid {α : Type} (state : MutableMemory α) (a : CopyArrayHeader) : Prop :=
  CopyMemoryValid state a.memory ∧ a.dimensions.length < 2 ^ 63 ∧
    (∀ d ∈ a.dimensions, 0 ≤ d.val) ∧ 1 ≤ a.refOffset.val ∧
    a.refOffset.val - 1 + (CopyArrayCount a : Int) ≤ a.memory.length.val

/-- A total observer distinguishes an absent physical cell from a present
slot marker. For boxed storage, None is a null element pointer; for inline
pointer-containing storage it is a null first pointer. For pointer-free/union
storage it is only a projection marker and does not imply unassignedness. This observes the existing cell-level memory runtime used by
base/array.jl:231-237,330-332; it does not execute any modeled Julia operation. -/
def CopyCell {α : Type} (state : MutableMemory α) (backing index : Nat) :
    Option (Option α) :=
  (state.memories[backing]?).bind (fun cells => cells[index]?)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Coordinate-wise mathematical validity, independently of the model's
recursive checkbounds implementation. A sole coordinate is linear; otherwise
provided coordinates select their respective dimensions, absent dimensions
have extent one, and omitted actual dimensions must be singleton. Source:
doc/src/manual/arrays.md:924-939,985-1033; base/essentials.jl:1124-1127. -/
def AssignedCoordinatesInBounds (a : CopyArrayHeader) (coordinates : List I) : Bool :=
  match coordinates with
  | [index] => decide (1 ≤ index.val ∧ index.val ≤ (CopyArrayCount a : Int))
  | _ =>
    (coordinates.zipIdx.all (fun item =>
      let extent : Int := ((a.dimensions[item.2]?).map (fun d => d.val)).getD 1
      decide (1 ≤ item.1.val ∧ item.1.val ≤ extent))) &&
    (a.dimensions.drop coordinates.length).all (fun dimension => dimension.val == 1)

/-- The zero-based mathematical column-major offset is a sum of coordinate
contributions times the products of preceding dimensions. No wrapped runtime
index or _sub2ind output appears in this observer. With a single index it is
index-1, and an empty index tuple has offset zero. Source:
doc/src/manual/arrays.md:933-939,985-1033. -/
def AssignedColumnOffset (a : CopyArrayHeader) (coordinates : List I) : Int :=
  (coordinates.zipIdx.map (fun item =>
    (item.1.val - 1) *
      ((a.dimensions.take item.2).map (fun dimension => dimension.val)).prod)).sum

/-- Independent specified assignment observation. Native pointer-free storage
has no undefined-reference state; for boxed or inline-pointer storage, the
physical cell's Option marker records whether the relevant pointer is non-null.
The address includes both the Memory-window and Array-reference offsets.
Source: base/essentials.jl:1124-1127; src/genericmemory.c:382-400. -/
def AssignedExpected {α : Type} (layout : JuliaLean.src.genericmemory_c.DictLayout)
    (before : MutableMemory α) (a : CopyArrayHeader) (coordinates : List I) : Bool :=
  if AssignedCoordinatesInBounds a coordinates then
    let address := a.memory.offset.val - 1 + a.refOffset.val - 1 +
      AssignedColumnOffset a coordinates
    (!JuliaLean.src.genericmemory_c.isBoxed layout.metadata &&
      decide (layout.metadata.memoryLayout.firstptr.val < 0)) ||
      (CopyCell before a.memory.backing address.toNat).join.isSome
  else
    false

/-- Every Array projection satisfying the necessary native size/window invariants
and every constructible Int-index tuple return
exactly the documented in-bounds definedness test, without changing any state.
All ranks, zero-sized dimensions, zero indices, linear indexing, omitted
trailing singleton dimensions and extra singleton indices are included.
No allocation-success hypothesis, supplied callee law, or model-output premise
is used. Undefined pointer slots give false, not UndefRefError; pointer-free
storage is assigned throughout its in-bounds region. Source:
base/array.jl:231-237; base/essentials.jl:1124-1127;
doc/src/manual/arrays.md:924-939,985-1033; src/genericmemory.c:382-400. -/
def AssignedArrayContract : Prop :=
  ∀ (α : Type) (layout : JuliaLean.src.genericmemory_c.DictLayout)
    (before : MutableMemory α) (a : CopyArrayHeader) (indices : TupleArgs I),
    CopyArrayValid before a →
      (assignedArray (α := α) layout a indices).run before =
        (.ok (AssignedExpected layout before a indices.values), before)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.Models1Group13

variable {Mod : Type}

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13

/-- Every native argument tuple in the selected nonempty Any literal overload
produces a fresh vector containing the same values, in the same order and with
unchanged identities, or raises the native allocation-size ArgumentError before
mutation. The complete native size domain is retained. The nonempty premise
selects base/array.jl:463-470 rather than the separate empty overload at 471.
The fixed boxed allocation uses eight bytes per element on the modeled platform;
no element-type failure or value conversion is possible at this boundary.
Documentation: doc/src/manual/arrays.md:334-338; allocation checks:
src/genericmemory.c:55-102. Julia source: base/array.jl:463-470. -/
def AnyValuesContract : Prop :=
  ∀ (α : Type) (args : TupleArgs α) (before : MutableMemory α),
    args.values ≠ [] →
    let n := args.values.length
    let run := (anyValues args).run before
    if n < 2 ^ 63 - 2 ∧ 8 * n < 2 ^ 63 - 2 then
      ∃ handle after, run = (.ok handle, after) ∧
        FreshVectorContents before after handle args.values
    else
      run = (.error (.argument
        "invalid GenericMemory size: the number of elements is either negative or too large for system address width"), before)
end JuliaLean.Proofs.base.array.Models1Group13


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean JuliaLean.base.array JuliaLean.Registry
open JuliaLean.Proofs.base.array.round4

/-- Omitted dimensions must be singleton; extra coordinates must be one. -/
def CartesianCoordinates : List Nat → List I → Bool
  | [], indices => indices.all (fun i => i.val == 1)
  | dimensions, [] => dimensions.all (· == 1)
  | d :: dimensions, i :: indices =>
      decide (1 ≤ i.val ∧ i.val ≤ (d : Int)) && CartesianCoordinates dimensions indices

def AllArityCartesianAccess : Prop :=
  ∀ (Tag α β : Type) (heap : VectorHeap α) (a : HeapArray Tag) (slots : List (Option α))
    (already : β → Bool) (asTyped : β → α) (convert : β → Except Error α)
    (value : β) (i₁ i₂ : I) (rest : List I),
    CartesianSetting heap a slots →
    let indices := i₁ :: i₂ :: rest
    let position := cartesianOffset a.dimensions indices
    let read := (getindexCartesian heapCheckbounds heapToLinear
      (fun a i => heapGet a.handle i) a i₁ i₂ rest).run heap
    let converted := if already value then .ok (asTyped value) else convert value
    let write := (setindexCartesian (fun x => if already x then some (asTyped x) else none)
      (fun x => liftM (convert x)) pure
      (setindexCartesianTyped heapCheckbounds heapToLinear
        (fun a k _ => pure (a.handle, k)) (fun ref x _ => heapSet ref.1 x ref.2))
      a value i₁ i₂ rest).run heap
    (¬ CartesianCoordinates a.dimensions indices → read = .error .bounds) ∧
    (CartesianCoordinates a.dimensions indices →
      (∀ x, slots[position.toNat]? = some (some x) → read = .ok (x, heap)) ∧
      (slots[position.toNat]? = some none → read = .error .undefinedReference)) ∧
    (∀ error, converted = .error error → write = .error error) ∧
    (∀ x, converted = .ok x →
      (¬ CartesianCoordinates a.dimensions indices → write = .error .bounds) ∧
      (CartesianCoordinates a.dimensions indices →
        write = .ok (a, heap.set a.handle (slots.set position.toNat (some x))))) ∧
    ((isassignedArray (m := VectorM α)
      (fun a is => match heapCheckboundsBool a is with
        | .ok b => pure b | .error _ => throw .bounds)
      (fun a => pure (heapAxes a))
      (fun dims is => match dimsSub2ind dims is with
        | .ok k => pure k | .error _ => throw .bounds)
      (fun a k _ => pure (a.handle, k))
      (fun ref => do let xs ← heapSlots ref.1
                     pure ((xs[(ref.2.val - 1).toNat]?.join).isSome))
      a indices).run heap =
        .ok (CartesianCoordinates a.dimensions indices &&
          (slots[position.toNat]?.join).isSome, heap))
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array
end JuliaLean.Proofs.base.array

open JuliaLean JuliaLean.base.array JuliaLean.base.array.Models1Group13
theorem JuliaLean.Proofs.base.array.Completion3.UnsetIntegerConversionFailures_proven : JuliaLean.Proofs.base.array.Completion3.UnsetIntegerConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.UnsetIntegerConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion3.unsetInteger]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion3.SafeSetindexConversionFailures_proven : JuliaLean.Proofs.base.array.Completion3.SafeSetindexConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion3.SafeSetindexConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion3.safeSetindexConvert]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion4.ScalarArrayConversionFailures_proven : JuliaLean.Proofs.base.array.Completion4.ScalarArrayConversionFailures := by
  unfold JuliaLean.Proofs.base.array.Completion4.ScalarArrayConversionFailures
  intros
  simp only [JuliaLean.base.array.Completion4.setindexScalar]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion6.TypedLiteralAllocationFailures_proven : JuliaLean.Proofs.base.array.Completion6.TypedLiteralAllocationFailures := by
  unfold JuliaLean.Proofs.base.array.Completion6.TypedLiteralAllocationFailures
  intros
  simp only [JuliaLean.base.array.Completion6.typedLiteral, JuliaLean.base.array.typedLiteral, JuliaLean.base.array.Completion6.vectorUndef]
  first
  | exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _
  | (apply JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind_right; exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)
  | (split <;> simp_all <;> exact JuliaLean.Proofs.base.array.Completion3.firstNativeFailure_bind _ _ _)


theorem JuliaLean.Proofs.base.array.Completion2.RawSafeindexReadAndBounds_proven : JuliaLean.Proofs.base.array.Completion2.RawSafeindexReadAndBounds := by
  unfold JuliaLean.Proofs.base.array.Completion2.RawSafeindexReadAndBounds
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion2.safeindexRaw, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.BooleanRangeIndexConversionErrors_proven : JuliaLean.Proofs.base.array.Completion4.BooleanRangeIndexConversionErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.BooleanRangeIndexConversionErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.getindexBoolRange, JuliaLean.base.array.getindexBoolRange, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.UnitRangeBoundsErrors_proven : JuliaLean.Proofs.base.array.Completion4.UnitRangeBoundsErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.UnitRangeBoundsErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.getindexUnitRange, JuliaLean.base.array.getindexUnitRange, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

theorem JuliaLean.Proofs.base.array.Completion4.UnitRangeAssignmentBoundsErrors_proven : JuliaLean.Proofs.base.array.Completion4.UnitRangeAssignmentBoundsErrors := by
  unfold JuliaLean.Proofs.base.array.Completion4.UnitRangeAssignmentBoundsErrors
  intros
  first
  | rfl
  | (repeat' (apply And.intro)) <;> intros <;> (try simp_all [JuliaLean.base.array.Completion4.setindexUnitRange, JuliaLean.base.array.setindexUnitRange, JuliaLean.Proofs.base.array.Completion.call, JuliaLean.Proofs.base.array.Completion2.call, JuliaLean.Proofs.base.array.Completion3.call, ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.run, StateT.bind, StateT.pure, StateT.map, StateT.modifyGet, MonadStateOf.modifyGet, MonadState.modifyGet, MonadLiftT.monadLift, MonadLift.monadLift, MonadExceptOf.throw, Functor.map, throw, throwThe, modify, modifyGet, bind, pure, List.append_assoc]) <;> (try rfl)

namespace JuliaLean.Proofs.base.array
def entriesGetindex1 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-getindex-unitrange", juliaFile := "base/array.jl",
    juliaFns := ["getindex(A::Array, I::AbstractUnitRange{<:Integer})"],
    statement := "`getindex(A::Array, I::AbstractUnitRange{<:Integer})` (array.jl:981) for every unit range of integers: a `UnitRange{T}` or `OneTo{T}` of every BitInteger type `T` (range.jl's `length`, `lengthUnit`/`lengthOneTo`; the range invariants `stop ≥ start - 1`, `stop ≥ 0`), and any other `AbstractUnitRange{<:Integer}` (a `UnitRange{BigInt}`, a user range: no Lean model) given by its `first` and `last` with the documented `length(r) = last - first + 1`.",
    source := "base/array.jl:981", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.RangeGetindexSpec, thm := some ``ChatGPTBatch1.ArrayRange.MultidimcovArrayV2GetindexUnitrange_proven,
    notes := "" },
  { id := "multidimcov-array-v2-setindex-range-colon", juliaFile := "base/array.jl",
    juliaFns := ["setindex!(A::Array{T}, X::Array{T}, I::AbstractUnitRange{Int})",
      "setindex!(A::Array{T}, X::Array{T}, c::Colon)"],
    statement := "A[lo:hi] = X raises BoundsError for a nonempty range outside A, then DimensionMismatch unless length(X) is the range length; otherwise slots lo..hi of A become X's slots and every other slot and array is unchanged. A[:] = X likewise replaces all of A when the lengths agree and raises DimensionMismatch otherwise.",
    source := "base/array.jl:1078-1096; indices.jl setindex_shape_check",
    status := .proven, prop := ``RangeColonSetindexSpec, thm := some ``rangeColonSetindexSpec}
]
def entriesGetindex2 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-getindex-colon", juliaFile := "base/array.jl",
    juliaFns := ["getindex(A::Array, ::Colon)"],
    statement := "Colon indexing returns a fresh vector with the same element type and every original stored value in linear order, preserving all existing arrays.",
    source := "base/array.jl:995-1002", status := .proven,
    prop := ``ColonArrayCopySpec, thm := some ``solArray.colonArrayCopySpec}
]
def entriesGetindex3 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-range-getindex-unsigned", juliaFile := "base/array.jl",
    juliaFns := ["getindex(v::AbstractRange, i::Integer)"],
    statement := "`getindex(v::AbstractRange, i::Integer)` (array.jl:3219): a `Bool` index raises `ArgumentError`; for `OneTo`, `UnitRange` and `StepRange` ranges of every BitInteger element type and an index of every BitInteger width, an index in `1:length(r)` returns the `i`-th element (`first(r) + (i - 1) * step(r)`) and any other index raises `BoundsError` (range.jl's `_getindex`/`getindex` models).",
    source := "base/array.jl:3219", status := .refuted,
    issue := "Searched JuliaLang/julia issues and PRs; matches #63679; see bugs/multidimcov-range-getindex-unsigned.yaml",
    prop := ``ScalarRangeIndexSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovRangeGetindexUnsigned_refuted,
    notes := "expected refuted: the file states ¬ ScalarRangeIndexSpec (theorem scalarRangeIndexSpec_refuted); repro/multidimcov-range-getindex-unsigned.jl; model missing: base/gmp.jl (the ranges are the OneTo, UnitRange and StepRange families of every BitInteger type; BigInt and user ranges are not instantiated)" },
  { id := "array-range-index-ordinary", juliaFile := "base/array.jl",
    juliaFns := ["getindex(v::AbstractRange, i::Integer)"],
    statement := "For ordinary signed Int indices, the array-file wrapper preserves the external range implementation's documented ordered-element indexing law and exact BoundsError; Bool indices are rejected before that implementation runs.",
    source := "base/array.jl:3219-3225; standard signed-index interface of range.jl",
    status := .proven, prop := ``OrdinaryRangeIndexSpec,
    thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayRangeIndexOrdinary_proven}
]
def entriesGetindex4 : List JuliaLean.Registry.Entry := [
  { id := "array-cartesian-read", juliaFile := "base/array.jl",
    juliaFns := ["getindex(A::Array, i1::Int, i2::Int, I::Int...)"],
    statement := "`getindex(A::Array, i1::Int, i2::Int, I::Int...)` (array.jl:974; `getindex` docstring in abstractarray.jl: \"Return a subset of array `A` as selected by the indices `inds`\") for one index per dimension, with abstractarray.jl's `checkbounds` and `_to_linear_index`: an index outside the array raises `BoundsError`; otherwise the element at the column-major position is returned (`UndefRefError` for an unassigned slot) and the heap is unchanged.",
    source := "base/array.jl:974", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.CartesianReadSpec,
    thm := some ``JuliaLean.Proofs.base.array.round4.cartesianReadSpec_proven,
    notes := "" }
]
def entriesGetindex5 : List JuliaLean.Registry.Entry := [
  { id := "array-cartesian-assignment", juliaFile := "base/array.jl",
    juliaFns := ["setindex!(A::Array{T}, x, i1::Int, i2::Int, I::Int...)",
      "_setindex!(A::Array{T}, x::T, i1::Int, i2::Int, I::Int...)"],
    statement := "`setindex!(A::Array{T}, x, i1::Int, i2::Int, I::Int...)` and its `_setindex!` (array.jl:1042, 1047; `setindex!` docstring in abstractarray.jl: \"Store values from array `X` within some subset of `A` as specified by `inds`\") for one index per dimension: `convert(T, x)` (any user conversion) runs first and its error propagates with the heap unchanged; an index outside the array then raises `BoundsError` with the heap unchanged; otherwise exactly the slot at the column-major position becomes `x` and `A` is returned.",
    source := "base/array.jl:1042", status := .proven,
    prop := ``CartesianAssignmentSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.ArrayCartesianAssignment_proven,
    notes := "" }
]
def entriesGetindex6 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-typed-literal", juliaFile := "base/array.jl",
    juliaFns := ["getindex(::Type{T}, vals...)", "getindex(::Type{Any}, vals...)"],
    statement := "Typed literals preserve the allocated element type and contain each converted value in order; the first failed conversion propagates, for homogeneous and mixed arguments.",
    source := "base/array.jl:445-470", status := .proven,
    prop := ``AllLiteralContents, thm := some ``allLiteralContents}
]
def entriesGetindex7 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-linear-access", juliaFile := "base/array.jl",
    juliaFns := ["unsetindex!(::Array, ::Int)", "isassigned(::Vector, ::Int)",
      "setindex!(::Array{T}, x, ::Int)", "_setindex!(::Array{T}, ::T, ::Int)"],
    statement := "Checked linear stores round-trip through reads, preserve other slots and shape, reject exactly out-of-range positions, propagate conversion failures without mutation, and unsetting clears only the selected boxed or pointer-containing inline slot while preserving union and pointer-free raw storage.",
    source := "base/array.jl:209-244,1031-1041; isassigned docstring", status := .proven,
    prop := ``LinearAccessComplete, thm := some ``JuliaLean.ChatGPT.Batch4.Group2.MultidimcovArrayV2LinearAccess_proven},
  { id := "multidimcov-array-v2-isassigned-linear", juliaFile := "base/array.jl",
    juliaFns := ["isassigned(::Array, ::Int...)"],
    statement := "`isassigned(a::Array, i::Int...)` (array.jl:231; `isassigned` docstring in abstractarray.jl: \"Return `true` if the value at the given index exists in an array, and `false` if it is out of bounds or has an undefined reference\") on a heap array, with `checkbounds(Bool, a, i...)` and `_sub2ind(size(a), i...)` of abstractarray.jl: one index per dimension gives `true` exactly when it is in bounds and the slot at its column-major position is assigned; a single linear index gives `true` exactly when it lies in `1:length(a)` and that slot is assigned; no index gives `true` exactly when every dimension is one and the only slot is assigned.",
    source := "base/array.jl:231", status := .proven,
    prop := ``JuliaLean.Proofs.base.array.round4.AssignmentLinearArraySpec, thm := some ``solArrayB.assignmentLinearArraySpec,
    notes := "" },
  { id := "multidimcov-array-v2-unsetindex-integer", juliaFile := "base/array.jl",
    juliaFns := ["unsetindex!(::Array, ::Integer)"],
    statement := "`unsetindex!(A::Array, i::Integer)` (array.jl:208, through `to_index(i)`: indices.jl's `convert(Int, i)`, `ArgumentError` for a `Bool`; and `unsetindex!(A::Array, i::Int)` at array.jl:210) on a vector of the store, for an index of every `Integer` type: a `Bool` raises `ArgumentError`, an index with no equal `Int` `InexactError`, and an index outside `1:length(A)` `BoundsError`, each with the store unchanged; otherwise the selected raw slot of `A` is cleared for boxed or pointer-containing inline storage and preserved for union or pointer-free storage, `A` is returned, and no array header changes.",
    source := "base/array.jl:208, array.jl:210", status := .todo,
    prop := ``JuliaLean.Proofs.base.array.round4.UnsetIntegerFullSpec, thm := none,
    notes := "" }
]
def entriesGetindex8 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-getindex-steprange", juliaFile := "base/array.jl",
    juliaFns := ["getindex(A::Array{S}, I::AbstractRange{Int}) where S"],
    statement := "A[r] for an Int range reads A[i] for i in r in order; the first index outside 1:length(A) raises BoundsError and the first unassigned slot UndefRefError before anything is built; otherwise the comprehension builder receives exactly the values A[i] in order.",
    source := "base/array.jl:1005-1007; getindex docstring", status := .proven, prop := ``RangeIndexGetSpec, thm := some ``rangeIndexGetSpec },
  { id := "multidimcov-array-v2-setindex-vector", juliaFile := "base/array.jl",
    juliaFns := ["setindex!(A::Array, X::AbstractArray, I::AbstractVector{Int})"],
    statement := "A[I] = X raises DimensionMismatch unless length(X) == length(I), then BoundsError for an index outside 1:length(A), with nothing changed; otherwise each X[k], converted, is stored at A[I[k]] in order (a repeated index keeps its last value) and every other slot and memory is unchanged; an unassigned X[k] or failing conversion raises after X[1:k-1] are stored.",
    source := "base/array.jl:1063-1075; indexed assignment (manual)", status := .proven, prop := ``VectorIndexSetSpec, thm := some ``ChatGPTBatch1.ArrayAssignment.MultidimcovArrayV2SetindexVector_proven }
]
def entriesGetindex9 : List JuliaLean.Registry.Entry := [
{ id := "array-safeindex-macro-escape", juliaFile := "base/array.jl",
  juliaFns := ["_safeindex(ex)"],
  statement := "The macro wraps every successful expansion in exactly one escape expression and propagates malformed-assignment errors.",
  source := "base/array.jl:132-134", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion2.SafeindexMacroEscape, thm := none,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-raw-safeindex-read-and-bounds", juliaFile := "base/array.jl",
  juliaFns := ["_safeindex(ex)"],
  statement := "Safe indexing preserves every original read argument without recursively rewriting it, and rejects an assignment expression with no left-hand argument.",
  source := "base/array.jl:135-156", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion2.RawSafeindexReadAndBounds, thm := some ``JuliaLean.Proofs.base.array.Completion2.RawSafeindexReadAndBounds_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-take-aliases-and-frame", juliaFile := "base/array.jl",
  juliaFns := ["_take!(dst::Array{T,N}, src::Array{T,N}) where {T,N}"],
  statement := "Taking an array makes the destination reference and size alias the source, returns the destination, and preserves every other header.",
  source := "base/array.jl:402-410", status := .todo,
  prop := ``JuliaLean.Proofs.base.array.Completion2.TakeAliasesAndFrame, thm := none,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesGetindex10 : List JuliaLean.Registry.Entry := [
{ id := "array-unset-integer-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["unsetindex!(A::Array, i::Integer)"],
  statement := "Integer conversion precedes every native vector-header, memory or storage operation; all errors, partial native states and divergence of conversion remain observable.",
  source := "base/array.jl:208-208", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.UnsetIntegerConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.UnsetIntegerConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesGetindex11 : List JuliaLean.Registry.Entry := [
{ id := "array-safe-setindex-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["__safe_setindex!(A::Vector{T}, x, i::Int) where {T}"],
  statement := "The safe converting setter propagates conversion failures and divergence before reading a vector reference or storing a value.",
  source := "base/array.jl:1059-1060", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion3.SafeSetindexConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion3.SafeSetindexConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesGetindex12 : List JuliaLean.Registry.Entry := [
{ id := "array-unit-range-bounds-errors", juliaFile := "base/array.jl",
  juliaFns := ["getindex(A::Array, I::AbstractUnitRange{<:Integer})"],
  statement := "Unit-range slicing checks bounds before length, axes, allocation or copying, retaining the exact error and world from the check.",
  source := "base/array.jl:981-990", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.UnitRangeBoundsErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.UnitRangeBoundsErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-boolean-range-index-conversion-errors", juliaFile := "base/array.jl",
  juliaFns := ["getindex(a::Array, r::AbstractUnitRange{Bool})"],
  statement := "Bool-range index conversion happens before indexing the array, retaining conversion errors and their effects.",
  source := "base/array.jl:993-993", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.BooleanRangeIndexConversionErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.BooleanRangeIndexConversionErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-scalar-array-conversion-failures", juliaFile := "base/array.jl",
  juliaFns := ["setindex!(A::Array{T}, x, i::Int) where {T}"],
  statement := "Every-rank scalar assignment converts and type-asserts the value before reading live dimensions, checking bounds or invoking native reference/store primitives.",
  source := "base/array.jl:1031-1035", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.ScalarArrayConversionFailures, thm := some ``JuliaLean.Proofs.base.array.Completion4.ScalarArrayConversionFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." },
{ id := "array-unit-range-assignment-bounds-errors", juliaFile := "base/array.jl",
  juliaFns := ["setindex!(A::Array{T}, X::Array{T}, I::AbstractUnitRange{Int}) where T"],
  statement := "Contiguous assignment checks destination bounds before length, shape compatibility or copying, retaining errors and preceding effects.",
  source := "base/array.jl:1078-1087", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion4.UnitRangeAssignmentBoundsErrors, thm := some ``JuliaLean.Proofs.base.array.Completion4.UnitRangeAssignmentBoundsErrors_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
def entriesGetindex13 : List JuliaLean.Registry.Entry := [
{ id := "array-typed-literal-allocation-failures", juliaFile := "base/array.jl",
  juliaFns := ["getindex(::Type{T}, vals...) where T"],
  statement := "A typed literal allocates before observing or converting any element. All native allocation errors, partial states and divergence remain observable.",
  source := "base/array.jl:445-461", status := .proven,
  prop := ``JuliaLean.Proofs.base.array.Completion6.TypedLiteralAllocationFailures, thm := some ``JuliaLean.Proofs.base.array.Completion6.TypedLiteralAllocationFailures_proven,
  notes := "Source order and error/state observations are retained. User-selected operations remain explicit; fixed Base helpers use their installed models." }
]
end JuliaLean.Proofs.base.array


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array.LegacyRetired

open JuliaLean.Registry
def entriesGetindex14 : List JuliaLean.Registry.Entry := [
  { id := "multidimcov-array-v2-cartesian-access", juliaFile := "base/array.jl",
    juliaFns := ["getindex(::Array, ::Int, ::Int, ::Int...)", "setindex!(::Array{T}, x, ::Int, ::Int, ::Int...)",
      "_setindex!(::Array{T}, ::T, ::Int, ::Int, ::Int...)", "isassigned(::Array, ::Int...)"],
    statement := "With two or more indices, any number of them: an index outside 1:d of its dimension, an extra index other than 1, or an omitted index for a dimension of size other than 1 throws BoundsError; otherwise A[I...] is the element at the column-major position of I, A[I...] = x writes exactly that slot (after conversion), and isassigned(A, I...) holds exactly when A[I...] returns.",
    source := "manual (column-major storage; omitted and extra indices); isassigned docstring base/essentials.jl:1112", status := .todo, prop := ``AllArityCartesianAccess,
    notes := "The old proof uses private array addressing. The installed native array reads, stores and assignment tests need the complete omitted/extra-index correspondence; existing Cartesian certificates assume one index per dimension." }
]
end JuliaLean.Proofs.base.array.LegacyRetired


open JuliaLean.src.genericmemory_c (DictLayout unsetCell boxedDictLayout)
open JuliaLean.Proofs.base.array (unsetClears expectedUnset unsetCell_result int64RuntimeLayout)
namespace JuliaLean.Proofs.base.array

open JuliaLean.Registry
def entriesGetindex15 : List JuliaLean.Registry.Entry := [
{ id := "array-isassigned-array-all-indices",
    juliaFile := "base/array.jl",
    juliaFns := ["isassigned(a::Array, i::Int...)"],
    statement := "For every Array projection satisfying the necessary native size/window invariants and every machine-sized Int-index tuple, isassigned returns the definedness of the mathematically selected column-major cell, or false for an out-of-bounds tuple, without mutation. The domain includes zero dimensions, no indices, linear indexing, omitted trailing singleton axes, extra singleton indices, shared-memory offsets and undefined reference slots; pointer-free cells are assigned in bounds.",
    source := "base/array.jl:231-237; base/essentials.jl:1124-1127; doc/src/manual/arrays.md:924-939,985-1033; src/genericmemory.c:382-400",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.AssignedArrayContract,
    thm := none,
    notes := "Uses existing abstractarray/essentials bounds, sub2ind, shared cell-memory runtime and GenericMemoryRef wrapper. Adds only the necessary local non-atomic native assignment projection; no shared runtime or frozen declaration changes. Physical byte-address aliasing, GC and concurrent writes remain outside the existing slot boundary." }
]
def entriesGetindex16 : List JuliaLean.Registry.Entry := [
{ id := "array-any-literal-values",
    juliaFile := "base/array.jl",
    juliaFns := ["getindex(::Type{Any}, vals...)"],
    statement := "Every constructible nonempty Any-literal argument tuple produces a fresh vector containing exactly those values, preserving their order and reference identities and all previous objects; native-size allocation rejection raises ArgumentError before mutation. Empty calls select the separate source471 overload.",
    source := "base/array.jl:463-470; doc/src/manual/arrays.md:334-338; src/genericmemory.c:55-102",
    status := .todo,
    prop := ``JuliaLean.Proofs.base.array.Models1Group13.AnyValuesContract,
    thm := none,
    notes := "Fixed existing boxed layout, existing mutableAllocate and safeSetindex1055/memoryWrite; no value conversion, supplied correctness law or allocation-success premise. Physical OOM and GC remain outside the installed cell-allocation runtime." }
]
end JuliaLean.Proofs.base.array

