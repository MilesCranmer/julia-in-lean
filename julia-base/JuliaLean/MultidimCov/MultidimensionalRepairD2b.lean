import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalRepairD2b

open JuliaLean.Registry

inductive Error where | inexact | bounds | shape | source (id : Nat) deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

inductive Event where
  | toIndices
  | checkbounds
  | shapeCheck
  | indexOffset
  | copyChunks (destination source count : Int)
  | convertBool (sourceIndex : Int)
  | writeBit (destinationIndex : Int) (value : Bool)
  | fillChunks (start count : Int) (value : Bool)
  | indexStyle
  | linearRoute
  | cartesianRoute
  | directRoute
  | tryGetindex
  deriving Repr, DecidableEq

structure Trace (A : Type) where
  events : List Event
  value : A
  deriving Repr, DecidableEq

def contiguousGetindex (destination : A) (sourceOffset length : Int) : Trace A :=
  ⟨[.indexOffset, .copyChunks 1 (sourceOffset + 1) length], destination⟩

def contiguousGetindexLoops (destination : A) (firstOffset innerLength : Int)
    (outerOffsets : List Int) : Trace A :=
  let copies := outerOffsets.zipIdx 0 |>.map fun pair =>
    Event.copyChunks (Int.ofNat pair.2 * innerLength + 1) (firstOffset + pair.1) innerLength
  ⟨[.indexOffset] ++ copies, destination⟩

def scalarGetindexLoops (destination : A) (sourceLinearIndices : List Int)
    (readBit : Int → Bool) : Trace A :=
  ⟨sourceLinearIndices.zipIdx 1 |>.map fun pair => .writeBit pair.2 (readBit pair.1), destination⟩

def copyConvertedBits (convert : X → Result Bool) (source : List X)
    (destinationStart sourceStart count : Int) : Result (List Event) :=
  copyLoop count.toNat 0
where
  copyLoop : Nat → Nat → Result (List Event)
    | 0, _ => .ok []
    | fuel + 1, offset =>
      if offset ≥ count.toNat then .ok [] else
      match source[(sourceStart - 1).toNat + offset]? with
      | none => .error .bounds
      | some value => match convert value with
        | .error error => .error error
        | .ok converted => match copyLoop fuel (offset + 1) with
          | .error error => .error error
          | .ok tail => .ok (.convertBool (sourceStart + offset) ::
              .writeBit (destinationStart + offset) converted :: tail)

def tryBoolConversion (equalZero equalOne : X → Bool) (value : X) : Result Bool :=
  if equalZero value then .ok false else if equalOne value then .ok true else .error .inexact

def uncheckedBoolConvert (equalOne : X → Bool) (value : X) : Bool := equalOne value

def optimizedCopyConvertedBits (equalZero equalOne : X → Bool) (source : List X)
    (destinationStart sourceStart count : Int) : Result (List Event) :=
  let selected := (source.drop (sourceStart - 1).toNat).take count.toNat
  match selected.mapM (tryBoolConversion equalZero equalOne) with
  | .error error => .error error
  | .ok converted => .ok (
      (selected.zipIdx sourceStart.toNat |>.map fun pair => .convertBool pair.2) ++
      (converted.zipIdx destinationStart.toNat |>.map fun pair => .writeBit pair.2 pair.1))

def contiguousSetindex (array : A) (toIndicesOk boundsOk shapeOk empty : Bool)
    (firstOffset length : Int) : Result (Trace A) :=
  if !toIndicesOk then .error (.source 1)
  else if !boundsOk then .error .bounds
  else if !shapeOk then .error .shape
  else if empty then .ok ⟨[.toIndices, .checkbounds, .shapeCheck], array⟩
  else .ok ⟨[.toIndices, .checkbounds, .shapeCheck, .indexOffset,
    .copyChunks (firstOffset + 1) 1 length], array⟩

def multidimensionalSetindex (array : A) (toIndicesOk boundsOk : Bool)
    (copyCalls : List (Int × Int × Int)) : Result (Trace A) :=
  if !toIndicesOk then .error (.source 1)
  else if !boundsOk then .error .bounds
  else .ok ⟨[.toIndices, .checkbounds, .shapeCheck] ++
    copyCalls.map fun call => .copyChunks call.1 call.2.1 call.2.2, array⟩

def delegatedSetindex (array : A) (result : Result A) : Result (Trace A) :=
  match result with | .error error => .error error | .ok _ => .ok ⟨[.toIndices, .indexStyle], array⟩

def fillContiguous (view : A) (convert : X → Result Bool) (value : X)
    (first count : Int) : Result (Trace A) :=
  if count = 0 then .ok ⟨[], view⟩ else match convert value with
  | .error error => .error error
  | .ok converted => .ok ⟨[.convertBool 0, .fillChunks first count converted], view⟩

def fillMultidimensional (view : A) (result : Result A) : Result (Trace A) :=
  match result with | .error error => .error error | .ok _ => .ok ⟨[], view⟩

def fillIndices (array : A) (convert : X → Result Bool) (value : X)
    (firstLength : Int) (emptyTail : Bool) (calls : List (Int × Int)) : Result (Trace A) :=
  match convert value with
  | .error error => .error error
  | .ok converted => if firstLength = 0 || emptyTail then .ok ⟨[.convertBool 0], array⟩
    else .ok ⟨[.convertBool 0] ++ calls.map fun call => .fillChunks call.1 firstLength converted, array⟩

def isassignedBitarray (sizes coordinates : List Int) (scalarAssigned : Int → Bool) : Bool :=
  if sizes.length + 1 ≠ coordinates.length then false else
  let first := coordinates.headD 0
  let rest := coordinates.drop 1
  if !(List.zip rest sizes).all (fun pair => 1 ≤ pair.1 && pair.1 ≤ pair.2) then false
  else
    let linear := (List.zip rest sizes).foldl (fun state pair =>
      (state.1 + (pair.1 - 1) * state.2, state.2 * pair.2)) (first, 1)
    scalarAssigned linear.1

def isassignedCartesian (toIndices : List I → Result (List J))
    (construct : List J → Result C) (redispatch : C → Result Bool) (indices : List I) : Result Bool :=
  match toIndices indices with
  | .error e => .error e
  | .ok converted => match construct converted with
    | .error e => .error e
    | .ok cartesian => redispatch cartesian

inductive Style where | linear | cartesian deriving Repr, DecidableEq
inductive AccessResult where | assigned | bounds | undef | other deriving Repr, DecidableEq

def isassignedGeneric (toIndices : List I → Result (List J)) (checkbounds : List J → Bool)
    (style : Style) (rank : Nat) (linearRoute cartesianRoute : List J → Result Bool)
    (directAccess : List J → AccessResult) (indices : List I) : Result Bool :=
  match toIndices indices with
  | .error error => .error error
  | .ok converted => if !checkbounds converted then .ok false else
    if style = .linear && converted.length ≠ 1 then linearRoute converted
    else if style = .cartesian && converted.length ≠ rank then cartesianRoute converted
    else match directAccess converted with
      | .assigned => .ok true
      | .bounds | .undef => .ok false
      | .other => .error (.source 9)

def Contract : Prop :=
  (∀ {A : Type} destination sourceOffset length,
    (contiguousGetindex (A := A) destination sourceOffset length).events =
      [.indexOffset, .copyChunks 1 (sourceOffset + 1) length] ∧
    (contiguousGetindex destination sourceOffset length).value = destination) ∧
  (∀ {X : Type} equalZero equalOne value,
    tryBoolConversion (X := X) equalZero equalOne value =
      if equalZero value then .ok false else if equalOne value then .ok true else .error .inexact) ∧
  (∀ {X : Type} equalOne value, uncheckedBoolConvert (X := X) equalOne value = equalOne value) ∧
  (∀ {A : Type} array toOk boundsOk shapeOk empty first length trace,
    contiguousSetindex (A := A) array toOk boundsOk shapeOk empty first length = .ok trace → trace.value = array) ∧
  (∀ {A X : Type} view convert value first count trace,
    fillContiguous (A := A) (X := X) view convert value first count = .ok trace → trace.value = view) ∧
  (∀ sizes coordinates scalarAssigned,
    isassignedBitarray sizes coordinates scalarAssigned = true →
      sizes.length + 1 = coordinates.length) ∧
  (∀ {I J C : Type} toIndices construct redispatch indices output,
    isassignedCartesian (I := I) (J := J) (C := C) toIndices construct redispatch indices = .ok output →
      ∃ converted cartesian, toIndices indices = .ok converted ∧ construct converted = .ok cartesian ∧
        redispatch cartesian = .ok output) ∧
  (∀ {I J : Type} toIndices checkbounds style rank linearRoute cartesianRoute direct indices,
    isassignedGeneric (I := I) (J := J) toIndices checkbounds style rank linearRoute cartesianRoute direct indices = .ok false →
      ∃ converted, toIndices indices = .ok converted ∧
        (!checkbounds converted = true ∨ direct converted = .bounds ∨ direct converted = .undef ∨
          linearRoute converted = .ok false ∨ cartesianRoute converted = .ok false))

theorem contract : Contract := by
  unfold Contract
  refine ⟨fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro A array toOk boundsOk shapeOk empty first length trace h
    cases toOk <;> cases boundsOk <;> cases shapeOk <;> cases empty <;>
      simp [contiguousSetindex] at h
    all_goals subst trace; rfl
  · intro A X view convert value first count trace h
    by_cases hz : count = 0
    · simp [fillContiguous, hz] at h; subst trace; rfl
    · cases hc : convert value <;> simp [fillContiguous, hz, hc] at h
      subst trace
      rfl
  · intro sizes coordinates scalarAssigned h
    by_cases hl : sizes.length + 1 = coordinates.length
    · exact hl
    · simp [isassignedBitarray, hl] at h
  · intro I J C toIndices construct redispatch indices output h
    cases ht : toIndices indices with
    | error e => simp [isassignedCartesian, ht] at h
    | ok converted =>
        cases hc : construct converted with
        | error e => simp [isassignedCartesian, ht, hc] at h
        | ok cartesian => exact ⟨converted, cartesian, rfl, hc,
            by simpa [isassignedCartesian, ht, hc] using h⟩
  · intro I J toIndices checkbounds style rank linearRoute cartesianRoute direct indices h
    cases ht : toIndices indices with
    | error e => simp [isassignedGeneric, ht] at h
    | ok converted =>
        refine ⟨converted, rfl, ?_⟩
        by_cases hb : checkbounds converted
        · cases style <;> simp [isassignedGeneric, ht, hb] at h ⊢ <;>
            split at h <;> simp_all <;> cases hd : direct converted <;> simp_all
        · exact Or.inl (by simp [hb])

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalRepairD2b
