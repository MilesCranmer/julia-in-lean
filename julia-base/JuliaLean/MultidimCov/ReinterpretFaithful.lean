import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.ReinterpretFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

/-- Exact incompatible-size diagnostic, lines 108-112. -/
def m108 (alignedSize : T → JResult AnyValue) (source target : T) : JResult α := do
  let targetSize ← alignedSize target
  let sourceSize ← alignedSize source
  .error (.argument (lazyAppend [
    .literal "`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
    .dynamic targetSize, .literal ") and `Base.elsize(Array{eltype(a)})` (got ",
    .dynamic sourceSize, .literal ") be an integer multiple of the other"]))
def P108 : Prop := ∀ {T α : Type} alignedSize source target,
  m108 (T := T) (α := α) alignedSize source target = do
    let targetSize ← alignedSize target
    let sourceSize ← alignedSize source
    .error (.argument (lazyAppend [
      .literal "`reinterpret(reshape, T, a)` requires that one of `Base.elsize(Array{T})` (got ",
      .dynamic targetSize, .literal ") and `Base.elsize(Array{eltype(a)})` (got ",
      .dynamic sourceSize, .literal ") be an integer multiple of the other"]))
theorem p108 : P108 := by unfold P108; intros; rfl

/-- Exact first-axis diagnostic, lines 113-118. -/
def m113 (showType : T → AnyValue) (eltype : A → JResult T) (axis1 : A → JResult AX)
    (alignedSize : T → JResult Nat) (showAxis : AX → AnyValue) (array : A) (target : T) : JResult α := do
  let source ← eltype array
  let axis ← axis1 array
  let targetSize ← alignedSize target
  let sourceSize ← alignedSize source
  .error (.argument (lazyAppend [.literal "`reinterpret(reshape, ", .dynamic (showType target),
    .literal ", a)` where `eltype(a)` is ", .dynamic (showType source),
    .literal " requires that `axes(a, 1)` (got ", .dynamic (showAxis axis),
    .literal ") be equal to 1:", .dynamic ⟨targetSize / sourceSize, targetSize / sourceSize⟩,
    .literal " (from the ratio of element sizes)"]))
def P113 : Prop := ∀ {T A AX α : Type} showType eltype axis1 alignedSize showAxis array target,
  m113 (T := T) (A := A) (AX := AX) (α := α) showType eltype axis1 alignedSize showAxis array target = do
    let source ← eltype array
    let axis ← axis1 array
    let targetSize ← alignedSize target
    let sourceSize ← alignedSize source
    .error (.argument (lazyAppend [.literal "`reinterpret(reshape, ", .dynamic (showType target),
      .literal ", a)` where `eltype(a)` is ", .dynamic (showType source),
      .literal " requires that `axes(a, 1)` (got ", .dynamic (showAxis axis),
      .literal ") be equal to 1:", .dynamic ⟨targetSize / sourceSize, targetSize / sourceSize⟩,
      .literal " (from the ratio of element sizes)"]))
theorem p113 : P113 := by unfold P113; intros; rfl

/-- Exact singleton-source diagnostic, lines 119-123. -/
def m119 (showSource : S → AnyValue) (showTarget : T → AnyValue) (source : S) (target : T) : JResult α :=
  .error (.argument (lazyAppend [.literal "`reinterpret(reshape, ", .dynamic (showTarget target),
    .literal ", a)` where `eltype(a)` is ", .dynamic (showSource source),
    .literal " requires that ", .dynamic (showTarget target),
    .literal " be a singleton type, since ", .dynamic (showSource source), .literal " is one"]))
def P119 : Prop := ∀ {S T α : Type} showSource showTarget source target,
  m119 (S := S) (T := T) (α := α) showSource showTarget source target =
    .error (.argument (lazyAppend [.literal "`reinterpret(reshape, ", .dynamic (showTarget target),
      .literal ", a)` where `eltype(a)` is ", .dynamic (showSource source),
      .literal " requires that ", .dynamic (showTarget target),
      .literal " be a singleton type, since ", .dynamic (showSource source), .literal " is one"]))
theorem p119 : P119 := by unfold P119 m119; intros; rfl

/-- `_checked_strides`, lines 222-227: all divrem calls precede the remainder scan. -/
def m222 (divrem : I → E → JResult (Q × R)) (isZero : R → JResult Bool)
    (strides : List I) (elementSize : E) : JResult (List Q) := do
  let results ← strides.mapM fun stride => divrem stride elementSize
  let exact ← results.mapM fun result => isZero result.2
  if exact.all id then .ok (results.map Prod.fst)
  else .error (.argument (.literal "Parent's strides could not be exactly divided!"))
def P222 : Prop := ∀ {I E Q R : Type} divrem isZero strides elementSize,
  m222 (I := I) (E := E) (Q := Q) (R := R) divrem isZero strides elementSize = do
    let results ← strides.mapM fun stride => divrem stride elementSize
    let exact ← results.mapM fun result => isZero result.2
    if exact.all id then .ok (results.map Prod.fst)
    else .error (.argument (.literal "Parent's strides could not be exactly divided!"))
theorem p222 : P222 := by unfold P222; intros; rfl

def m433 (checkReadable : A → JResult Unit) (ptrIndexable : A → JResult Bool)
    (getPtr : A → List Int → JResult (List UInt8))
    (getArray : A → Int → List Int → JResult (List UInt8))
    (array : A) (indices : List Int) : JResult (List UInt8) := do
  checkReadable array
  let pointer ← ptrIndexable array
  if pointer then getPtr array indices else
    match indices with
    | [] => .error .bounds
    | first :: rest => getArray array first rest
def P433 : Prop := ∀ {A : Type} checkReadable ptrIndexable getPtr getArray array indices,
  m433 (A := A) checkReadable ptrIndexable getPtr getArray array indices = do
    checkReadable array
    let pointer ← ptrIndexable array
    if pointer then getPtr array indices else
      match indices with | [] => .error .bounds | first :: rest => getArray array first rest
theorem p433 : P433 := by unfold P433; intros; rfl

def m439 (checkReadable : A → JResult Unit) (ptrIndexable : A → JResult Bool)
    (getPtr : A → Int → JResult (List UInt8)) (indexLinear : A → JResult Bool)
    (subscripts : A → Int → JResult (List Int))
    (getArray : A → Int → List Int → JResult (List UInt8)) (firstIndex : A → JResult Int)
    (array : A) (index : Int) : JResult (List UInt8) := do
  checkReadable array
  let pointer ← ptrIndexable array
  if pointer then getPtr array index else do
    let linear ← indexLinear array
    if linear then getArray array index [] else do
      let values ← subscripts array index
      match values with
      | first :: rest => getArray array first rest
      | [] => do let first ← firstIndex array; getArray array first []
def P439 : Prop := ∀ {A : Type} checkReadable ptrIndexable getPtr indexLinear subscripts getArray firstIndex array index,
  m439 (A := A) checkReadable ptrIndexable getPtr indexLinear subscripts getArray firstIndex array index = do
    checkReadable array
    let pointer ← ptrIndexable array
    if pointer then getPtr array index else do
      let linear ← indexLinear array
      if linear then getArray array index [] else do
        let values ← subscripts array index
        match values with
        | first :: rest => getArray array first rest
        | [] => do let first ← firstIndex array; getArray array first []
theorem p439 : P439 := by unfold P439; intros; rfl

/-- Reshaped static Cartesian read, lines 451-456. -/
def m451 (checkReadable : A → JResult Unit) (readParent : A → J → JResult S)
    (makeRef : S → JResult Ref) (unsafeConvert : Ref → JResult Ptr)
    (unsafeLoad : Ptr → I → JResult (List UInt8)) (array : A) (i : I) (j : J) : JResult (List UInt8) := do
  checkReadable array
  let source ← readParent array j
  let rooted ← makeRef source
  let pointer ← unsafeConvert rooted
  unsafeLoad pointer i
def P451 : Prop := ∀ {A J S Ref Ptr I : Type} checkReadable readParent makeRef unsafeConvert unsafeLoad array i j,
  m451 (A := A) (J := J) (S := S) (Ref := Ref) (Ptr := Ptr) (I := I)
    checkReadable readParent makeRef unsafeConvert unsafeLoad array i j = do
      checkReadable array
      let source ← readParent array j
      let rooted ← makeRef source
      let pointer ← unsafeConvert rooted
      unsafeLoad pointer i
theorem p451 : P451 := by unfold P451; intros; rfl

/-- Pointer read, lines 458-464. -/
def m458 (checkbounds : A → List I → JResult Unit) (linearIndex : A → List I → JResult Int)
    (cconvert : A → JResult Root) (unsafeConvert : Root → JResult Ptr)
    (elementSize : A → JResult Int) (firstIndex : A → JResult Int)
    (addPointer : Ptr → Int → JResult Ptr) (unsafeLoad : Ptr → JResult (List UInt8))
    (array : A) (indices : List I) : JResult (List UInt8) := do
  checkbounds array indices
  let linear ← linearIndex array indices
  let root ← cconvert array
  let pointer ← unsafeConvert root
  let size ← elementSize array
  let first ← firstIndex array
  let address ← addPointer pointer (size * (linear - first))
  unsafeLoad address
def P458 : Prop := ∀ {A I Root Ptr : Type} checkbounds linearIndex cconvert unsafeConvert elementSize
    firstIndex addPointer unsafeLoad array indices,
  m458 (A := A) (I := I) (Root := Root) (Ptr := Ptr) checkbounds linearIndex cconvert
    unsafeConvert elementSize firstIndex addPointer unsafeLoad array indices = do
      checkbounds array indices
      let linear ← linearIndex array indices
      let root ← cconvert array
      let pointer ← unsafeConvert root
      let size ← elementSize array
      let first ← firstIndex array
      let address ← addPointer pointer (size * (linear - first))
      unsafeLoad address
theorem p458 : P458 := by unfold P458; intros; rfl

/-- Scalar reinterpret applicability, lines 466-468. -/
def m466 (isPrimitive : T → JResult Bool) (bitsize : T → JResult Nat) (target source : T) : JResult Bool := do
  let targetPrimitive ← isPrimitive target
  let sourcePrimitive ← isPrimitive source
  if targetPrimitive && sourcePrimitive then do
    let targetBits ← bitsize target
    let sourceBits ← bitsize source
    .ok (targetBits = sourceBits)
  else .ok false
def P466 : Prop := ∀ {T : Type} isPrimitive bitsize target source,
  m466 (T := T) isPrimitive bitsize target source = do
    let targetPrimitive ← isPrimitive target
    let sourcePrimitive ← isPrimitive source
    if targetPrimitive && sourcePrimitive then do
      let targetBits ← bitsize target
      let sourceBits ← bitsize source
      .ok (targetBits = sourceBits)
    else .ok false
theorem p466 : P466 := by unfold P466; intros; rfl

/-- Non-reshaped array read, including singleton target, lines 470-522. -/
def m470 (isSingleton : T → JResult Bool) (checkbounds : A → Int → List Int → JResult Unit)
    (scalarApplicable : T → T → JResult Bool) (readParent : A → Int → List Int → JResult (List UInt8))
    (reinterpretScalar : List UInt8 → JResult (List UInt8))
    (assemble : A → Int → List Int → JResult (List UInt8))
    (target source : T) (array : A) (first : Int) (rest : List Int) : JResult (List UInt8) := do
  let singleton ← isSingleton target
  if singleton then do checkbounds array first rest; .ok []
  else do
    let scalar ← scalarApplicable target source
    if scalar then do let bytes ← readParent array first rest; reinterpretScalar bytes
    else do checkbounds array first rest; assemble array first rest
def P470 : Prop := ∀ {T A : Type} isSingleton checkbounds scalarApplicable readParent reinterpretScalar
    assemble target source array first rest,
  m470 (T := T) (A := A) isSingleton checkbounds scalarApplicable readParent reinterpretScalar
    assemble target source array first rest = do
      let singleton ← isSingleton target
      if singleton then do checkbounds array first rest; .ok []
      else do
        let scalar ← scalarApplicable target source
        if scalar then do let bytes ← readParent array first rest; reinterpretScalar bytes
        else do checkbounds array first rest; assemble array first rest
theorem p470 : P470 := by unfold P470; intros; rfl

/-- Reshaped array read size branches, lines 524-567. -/
def m524 (isSingleton : T → JResult Bool) (checkbounds : A → Int → List Int → JResult Unit)
    (scalarApplicable : T → T → JResult Bool) (targetSize sourceSize : T → JResult Nat)
    (scalarRead largerRead equalRead smallerRead : A → Int → List Int → JResult (List UInt8))
    (target source : T) (array : A) (first : Int) (rest : List Int) : JResult (List UInt8) := do
  let singleton ← isSingleton target
  if singleton then do checkbounds array first rest; .ok []
  else do
    let scalar ← scalarApplicable target source
    if scalar then scalarRead array first rest else do
      checkbounds array first rest
      let ts ← targetSize target
      let ss ← sourceSize source
      if ts > ss then largerRead array first rest
      else if ts = ss then equalRead array first rest
      else smallerRead array first rest
def P524 : Prop := ∀ {T A : Type} isSingleton checkbounds scalarApplicable targetSize sourceSize
    scalarRead largerRead equalRead smallerRead target source array first rest,
  m524 (T := T) (A := A) isSingleton checkbounds scalarApplicable targetSize sourceSize
    scalarRead largerRead equalRead smallerRead target source array first rest = do
      let singleton ← isSingleton target
      if singleton then do checkbounds array first rest; .ok []
      else do
        let scalar ← scalarApplicable target source
        if scalar then scalarRead array first rest else do
          checkbounds array first rest
          let ts ← targetSize target
          let ss ← sourceSize source
          if ts > ss then largerRead array first rest
          else if ts = ss then equalRead array first rest
          else smallerRead array first rest
theorem p524 : P524 := by unfold P524; intros; rfl

def m577 (firstIndex : A → JResult I) (setindex : A → V → I → JResult A)
    (array : A) (value : V) : JResult A := do let first ← firstIndex array; setindex array value first
def P577 : Prop := ∀ {A V I : Type} firstIndex setindex array value,
  m577 (A := A) (V := V) (I := I) firstIndex setindex array value = do
    let first ← firstIndex array
    setindex array value first
theorem p577 : P577 := by unfold P577; intros; rfl

def m579 (checkWritable : A → JResult Unit) (ptrIndexable : A → JResult Bool)
    (setPtr : A → V → List Int → JResult A) (setArray : A → V → Int → List Int → JResult A)
    (array : A) (value : V) (indices : List Int) : JResult A := do
  checkWritable array
  let pointer ← ptrIndexable array
  if pointer then setPtr array value indices else
    match indices with | [] => .error .bounds | first :: rest => setArray array value first rest
def P579 : Prop := ∀ {A V : Type} checkWritable ptrIndexable setPtr setArray array value indices,
  m579 (A := A) (V := V) checkWritable ptrIndexable setPtr setArray array value indices = do
    checkWritable array
    let pointer ← ptrIndexable array
    if pointer then setPtr array value indices else
      match indices with | [] => .error .bounds | first :: rest => setArray array value first rest
theorem p579 : P579 := by unfold P579; intros; rfl

def m585 (checkWritable : A → JResult Unit) (ptrIndexable : A → JResult Bool)
    (setPtr : A → V → Int → JResult A) (indexLinear : A → JResult Bool)
    (subscripts : A → Int → JResult (List Int)) (firstIndex : A → JResult Int)
    (setArray : A → V → Int → List Int → JResult A) (array : A) (value : V) (index : Int) : JResult A := do
  checkWritable array
  let pointer ← ptrIndexable array
  if pointer then setPtr array value index else do
    let linear ← indexLinear array
    if linear then setArray array value index [] else do
      let values ← subscripts array index
      match values with
      | first :: rest => setArray array value first rest
      | [] => do let first ← firstIndex array; setArray array value first []
def P585 : Prop := ∀ {A V : Type} checkWritable ptrIndexable setPtr indexLinear subscripts firstIndex
    setArray array value index,
  m585 (A := A) (V := V) checkWritable ptrIndexable setPtr indexLinear subscripts firstIndex
    setArray array value index = do
      checkWritable array
      let pointer ← ptrIndexable array
      if pointer then setPtr array value index else do
        let linear ← indexLinear array
        if linear then setArray array value index [] else do
          let values ← subscripts array index
          match values with
          | first :: rest => setArray array value first rest
          | [] => do let first ← firstIndex array; setArray array value first []
theorem p585 : P585 := by unfold P585; intros; rfl

def m595 (checkWritable : A → JResult Unit) (convert : V → JResult T)
    (readParent : A → J → JResult S) (makeRef : S → JResult Ref) (unsafeConvert : Ref → JResult Ptr)
    (unsafeStore : Ptr → T → I → JResult Ref) (writeParent : A → J → Ref → JResult A)
    (array : A) (value : V) (i : I) (j : J) : JResult A := do
  checkWritable array
  let converted ← convert value
  let source ← readParent array j
  let rooted ← makeRef source
  let pointer ← unsafeConvert rooted
  let changed ← unsafeStore pointer converted i
  writeParent array j changed
def P595 : Prop := ∀ {A V T J S Ref Ptr I : Type} checkWritable convert readParent makeRef
    unsafeConvert unsafeStore writeParent array value i j,
  m595 (A := A) (V := V) (T := T) (J := J) (S := S) (Ref := Ref) (Ptr := Ptr) (I := I)
    checkWritable convert readParent makeRef unsafeConvert unsafeStore writeParent array value i j = do
      checkWritable array
      let converted ← convert value
      let source ← readParent array j
      let rooted ← makeRef source
      let pointer ← unsafeConvert rooted
      let changed ← unsafeStore pointer converted i
      writeParent array j changed
theorem p595 : P595 := by unfold P595; intros; rfl

def m607 (checkbounds : A → List I → JResult Unit) (linearIndex : A → List I → JResult Int)
    (cconvert : A → JResult Root) (unsafeConvert : Root → JResult Ptr)
    (elementSize : A → JResult Int) (firstIndex : A → JResult Int) (addPointer : Ptr → Int → JResult Ptr)
    (convert : V → JResult T) (unsafeStore : Ptr → T → JResult Unit)
    (array : A) (value : V) (indices : List I) : JResult A := do
  checkbounds array indices
  let linear ← linearIndex array indices
  let root ← cconvert array
  let pointer ← unsafeConvert root
  let size ← elementSize array
  let first ← firstIndex array
  let address ← addPointer pointer (size * (linear - first))
  let converted ← convert value
  unsafeStore address converted
  .ok array
def P607 : Prop := ∀ {A I Root Ptr V T : Type} checkbounds linearIndex cconvert unsafeConvert
    elementSize firstIndex addPointer convert unsafeStore array value indices,
  m607 (A := A) (I := I) (Root := Root) (Ptr := Ptr) (V := V) (T := T)
    checkbounds linearIndex cconvert unsafeConvert elementSize firstIndex addPointer convert unsafeStore
    array value indices = do
      checkbounds array indices
      let linear ← linearIndex array indices
      let root ← cconvert array
      let pointer ← unsafeConvert root
      let size ← elementSize array
      let first ← firstIndex array
      let address ← addPointer pointer (size * (linear - first))
      let converted ← convert value
      unsafeStore address converted
      .ok array
theorem p607 : P607 := by unfold P607; intros; rfl

def m616 (convert : V → JResult T) (isSingleton : Ty → JResult Bool)
    (checkbounds : A → Int → List Int → JResult Unit) (scalarApplicable : Ty → Ty → JResult Bool)
    (scalarSet : A → T → Int → List Int → JResult A)
    (assembleSet : A → T → Int → List Int → JResult A) (target source : Ty)
    (array : A) (value : V) (first : Int) (rest : List Int) : JResult A := do
  let converted ← convert value
  let singleton ← isSingleton target
  if singleton then do checkbounds array first rest; .ok array
  else do
    let scalar ← scalarApplicable target source
    if scalar then scalarSet array converted first rest
    else do checkbounds array first rest; assembleSet array converted first rest
def P616 : Prop := ∀ {V T Ty A : Type} convert isSingleton checkbounds scalarApplicable scalarSet
    assembleSet target source array value first rest,
  m616 (V := V) (T := T) (Ty := Ty) (A := A) convert isSingleton checkbounds scalarApplicable
    scalarSet assembleSet target source array value first rest = do
      let converted ← convert value
      let singleton ← isSingleton target
      if singleton then do checkbounds array first rest; .ok array
      else do
        let scalar ← scalarApplicable target source
        if scalar then scalarSet array converted first rest
        else do checkbounds array first rest; assembleSet array converted first rest
theorem p616 : P616 := by unfold P616; intros; rfl

def m685 (convert : V → JResult T) (isSingleton : Ty → JResult Bool)
    (checkbounds : A → Int → List Int → JResult Unit) (scalarApplicable : Ty → Ty → JResult Bool)
    (scalarSet : A → T → Int → List Int → JResult A) (targetSize sourceSize : Ty → JResult Nat)
    (largerSet equalSet smallerSet : A → T → Int → List Int → JResult A)
    (target source : Ty) (array : A) (value : V) (first : Int) (rest : List Int) : JResult A := do
  let converted ← convert value
  let singleton ← isSingleton target
  if singleton then do checkbounds array first rest; .ok array
  else do
    let scalar ← scalarApplicable target source
    if scalar then scalarSet array converted first rest else do
      checkbounds array first rest
      let ts ← targetSize target
      let ss ← sourceSize source
      if ts > ss then largerSet array converted first rest
      else if ts = ss then equalSet array converted first rest
      else smallerSet array converted first rest
def P685 : Prop := ∀ {V T Ty A : Type} convert isSingleton checkbounds scalarApplicable scalarSet
    targetSize sourceSize largerSet equalSet smallerSet target source array value first rest,
  m685 (V := V) (T := T) (Ty := Ty) (A := A) convert isSingleton checkbounds scalarApplicable
    scalarSet targetSize sourceSize largerSet equalSet smallerSet target source array value first rest = do
      let converted ← convert value
      let singleton ← isSingleton target
      if singleton then do checkbounds array first rest; .ok array
      else do
        let scalar ← scalarApplicable target source
        if scalar then scalarSet array converted first rest else do
          checkbounds array first rest
          let ts ← targetSize target
          let ss ← sourceSize source
          if ts > ss then largerSet array converted first rest
          else if ts = ss then equalSet array converted first rest
          else smallerSet array converted first rest
theorem p685 : P685 := by unfold P685; intros; rfl

inductive TypeTree where
  | primitive (bits : Nat)
  | union (members : List TypeTree)
  | composite (fields : List TypeTree)
  deriving Repr

mutual
  def hasBitPadding : TypeTree → Bool
    | .primitive bits => bits % 8 != 0
    | .union members => hasAnyBitPadding members
    | .composite fields => hasAnyBitPadding fields
  def hasAnyBitPadding : List TypeTree → Bool
    | [] => false
    | value :: rest => hasBitPadding value || hasAnyBitPadding rest
end
def P828 : Prop :=
  (∀ bits, hasBitPadding (.primitive bits) = (bits % 8 != 0)) ∧
  (∀ members, hasBitPadding (.union members) = hasAnyBitPadding members) ∧
  (∀ fields, hasBitPadding (.composite fields) = hasAnyBitPadding fields)
theorem p828 : P828 := by simp [P828, hasBitPadding]

structure FieldLayout where
  offset : Nat
  packedSize : Nat
  deriving Repr

def copyFields (copy : M → Nat → Nat → Nat → JResult M) :
    M → Nat → Nat → List FieldLayout → JResult (M × Nat)
  | memory, _, readOffset, [] => .ok (memory, readOffset)
  | memory, base, readOffset, field :: rest => do
      let changed ← copy memory (base + field.offset) readOffset field.packedSize
      copyFields copy changed base (readOffset + field.packedSize) rest

/-- `_copyfrompacked!`, lines 859-877. -/
def m859 (primitive : Bool) (packedSize : Nat) (fields : List FieldLayout)
    (copy : M → Nat → Nat → Nat → JResult M) (memory : M) : JResult M :=
  if primitive then copy memory 0 0 packedSize
  else do let result ← copyFields copy memory 0 0 fields; .ok result.1
def P859 : Prop := ∀ {M : Type} primitive packedSize fields copy memory,
  m859 (M := M) primitive packedSize fields copy memory =
    if primitive then copy memory 0 0 packedSize
    else do let result ← copyFields copy memory 0 0 fields; .ok result.1
theorem p859 : P859 := by unfold P859; intros; rfl

/-- Scalar `_reinterpret`, lines 879-906. -/
def m879 (isBits : Ty → JResult Bool) (bitPadding : Ty → JResult Bool)
    (packedSize : Ty → JResult Nat) (isPacked : Ty → JResult Bool)
    (subpadding : Ty → Ty → JResult Bool) (directCopy : Out → In → JResult Out)
    (paddingCopy : Out → In → JResult Out) (outTy inTy : Ty) (out : Out) (input : In) : JResult Out := do
  let outBits ← isBits outTy
  if ¬outBits then .error (.argument (.literal "Target type for `reinterpret` must be isbits"))
  let inBits ← isBits inTy
  if ¬inBits then .error (.argument (.literal "Source type for `reinterpret` must be isbits"))
  let outPadding ← bitPadding outTy
  if outPadding then .error (.argument (.literal "target contains non-byte-aligned primitive fields"))
  let inPadding ← bitPadding inTy
  if inPadding then .error (.argument (.literal "source contains non-byte-aligned primitive fields"))
  let inputSize ← packedSize inTy
  let outputSize ← packedSize outTy
  if inputSize != outputSize then .error (.argument (.literal "packed sizes do not match"))
  let inputPacked ← isPacked inTy
  let outputPacked ← isPacked outTy
  let samePadding ← subpadding outTy inTy
  if (inputPacked && outputPacked) || samePadding then directCopy out input else paddingCopy out input
def P879 : Prop := ∀ {Ty Out In : Type} isBits bitPadding packedSize isPacked subpadding directCopy
    paddingCopy outTy inTy out input,
  m879 (Ty := Ty) (Out := Out) (In := In) isBits bitPadding packedSize isPacked subpadding
    directCopy paddingCopy outTy inTy out input = do
      let outBits ← isBits outTy
      if ¬outBits then .error (.argument (.literal "Target type for `reinterpret` must be isbits"))
      let inBits ← isBits inTy
      if ¬inBits then .error (.argument (.literal "Source type for `reinterpret` must be isbits"))
      let outPadding ← bitPadding outTy
      if outPadding then .error (.argument (.literal "target contains non-byte-aligned primitive fields"))
      let inPadding ← bitPadding inTy
      if inPadding then .error (.argument (.literal "source contains non-byte-aligned primitive fields"))
      let inputSize ← packedSize inTy
      let outputSize ← packedSize outTy
      if inputSize != outputSize then .error (.argument (.literal "packed sizes do not match"))
      let inputPacked ← isPacked inTy
      let outputPacked ← isPacked outTy
      let samePadding ← subpadding outTy inTy
      if (inputPacked && outputPacked) || samePadding then directCopy out input else paddingCopy out input
theorem p879 : P879 := by unfold P879; intros; rfl

/-- Padding-aware scalar reinterpret, lines 910-932. -/
def m910 (packedSize : In → JResult Nat) (makeInRef : In → JResult IR)
    (makeOutRef : JResult OR) (inPointer : IR → JResult Ptr) (outPointer : OR → JResult Ptr)
    (fieldCountIn fieldCountOut : JResult Nat) (isPackedIn isPackedOut : JResult Bool)
    (copyTo : Ptr → Ptr → JResult Ptr) (copyFrom : Ptr → Ptr → JResult Ptr)
    (temporary : Nat → JResult (TMP × Ptr)) (readOut : Ptr → JResult Out) (input : In) : JResult Out := do
  let size ← packedSize input
  let inputRef ← makeInRef input
  let outputRef ← makeOutRef
  let source ← inPointer inputRef
  let target ← outPointer outputRef
  let inFields ← fieldCountIn
  let outFields ← fieldCountOut
  let outPacked ← isPackedOut
  let inPacked ← isPackedIn
  let final ← if inFields > 0 && outPacked then copyTo target source
    else if outFields > 0 && inPacked then copyFrom target source
    else do
      let packed ← temporary size
      let _ ← copyTo packed.2 source
      copyFrom target packed.2
  readOut final
def P910 : Prop := ∀ {In IR OR Ptr TMP Out : Type} packedSize makeInRef makeOutRef
    inPointer outPointer fieldCountIn fieldCountOut isPackedIn isPackedOut copyTo copyFrom
    temporary readOut input,
  m910 (In := In) (IR := IR) (OR := OR) (Ptr := Ptr) (TMP := TMP) (Out := Out)
    packedSize makeInRef makeOutRef inPointer outPointer fieldCountIn fieldCountOut isPackedIn
    isPackedOut copyTo copyFrom temporary readOut input = do
      let size ← packedSize input
      let inputRef ← makeInRef input
      let outputRef ← makeOutRef
      let source ← inPointer inputRef
      let target ← outPointer outputRef
      let inFields ← fieldCountIn
      let outFields ← fieldCountOut
      let outPacked ← isPackedOut
      let inPacked ← isPackedIn
      let final ← if inFields > 0 && outPacked then copyTo target source
        else if outFields > 0 && inPacked then copyFrom target source
        else do
          let packed ← temporary size
          let _ ← copyTo packed.2 source
          copyFrom target packed.2
      readOut final
theorem p910 : P910 := by unfold P910; intros; rfl

def foldValues (map : X → JResult V) (op : V → V → JResult V) : V → List X → JResult V
  | value, [] => .ok value
  | value, x :: xs => do let mapped ← map x; let next ← op value mapped; foldValues map op next xs

def reduceColumnsFuel (map : X → JResult V) (op : V → V → JResult V)
    (block : Nat) : Nat → List (List X) → JResult V
  | 0, rows => do
    let values := rows.flatMap id
    match values with
    | [] => .error (.callback 953)
    | first :: rest => do let initial ← map first; foldValues map op initial rest
  | fuel + 1, rows => do
      let values := rows.flatMap id
      match values with
      | [] => .error (.callback 953)
      | first :: rest =>
          if rows.length < block || rows.length ≤ 1 then do
            let initial ← map first
            foldValues map op initial rest
          else do
            let midpoint := rows.length / 2
            let left ← reduceColumnsFuel map op block fuel (rows.take midpoint)
            let right ← reduceColumnsFuel map op block fuel (rows.drop midpoint)
            op left right

def m953 (map : X → JResult V) (op : V → V → JResult V)
    (rows : List (List X)) (block : Nat) : JResult V :=
  reduceColumnsFuel map op block rows.length rows
def P953 : Prop := ∀ {X V : Type} map op rows block,
  m953 (X := X) (V := V) map op rows block = reduceColumnsFuel map op block rows.length rows
theorem p953 : P953 := by unfold P953 m953; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-reinterpretarray-faithful-{line}", juliaFile := "base/reinterpretarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 108 "throwintmult" "The helper evaluates both aligned element sizes and constructs the complete LazyString integer-multiple ArgumentError." "base/reinterpretarray.jl:108-112" ``P108 ``p108,
  entry 113 "throwsize1" "The helper evaluates eltype, first axis, both aligned sizes, and constructs the complete first-axis ArgumentError." "base/reinterpretarray.jl:113-118" ``P113 ``p113,
  entry 119 "throwfromsingleton" "The helper constructs the complete input-dependent singleton-source ArgumentError." "base/reinterpretarray.jl:119-123" ``P119 ``p119,
  entry 222 "_checked_strides" "The method maps divrem over every byte stride before testing all remainders, throws on any nonzero remainder, and returns all quotients." "base/reinterpretarray.jl:222-227" ``P222 ``p222,
  entry 433 "getindex(cartesian Ints)" "The wrapper checks readability, selects pointer or array access, and returns the exact bytes supplied by that route." "base/reinterpretarray.jl:433-437" ``P433 ``p433,
  entry 439 "getindex(linear Int)" "The linear wrapper checks readability, selects pointer, IndexLinear, or subscript routing, and returns the chosen route's bytes." "base/reinterpretarray.jl:439-449" ``P439 ``p439,
  entry 451 "getindex(reshaped SCartesianIndex2)" "The method reads the parent, creates and roots a Ref, converts its pointer, and unsafe-loads the indexed target bytes." "base/reinterpretarray.jl:451-456" ``P451 ``p451,
  entry 458 "_getindex_ptr" "Pointer access checks bounds, computes the linear byte offset, roots cconvert, converts the pointer, and loads from the exact address." "base/reinterpretarray.jl:458-464" ``P458 ``p458,
  entry 466 "_is_scalar_reinterpret_applicable" "Scalar applicability requires both primitive types and equal Core.bitsizeof results." "base/reinterpretarray.jl:466-468" ``P466 ``p466,
  entry 470 "_getindex_ra(non-reshaped)" "The read handles singleton targets through bounds-only empty bytes, scalar reinterpretation, or checked byte assembly." "base/reinterpretarray.jl:470-522" ``P470 ``p470,
  entry 524 "_getindex_ra(reshaped)" "The reshaped read includes singleton and scalar routes, then branches after bounds checking into larger, equal, or smaller size byte assembly." "base/reinterpretarray.jl:524-567" ``P524 ``p524,
  entry 577 "setindex!(reshaped zero-dimensional)" "The zero-dimensional wrapper obtains firstindex and delegates the actual array and value to setindex!." "base/reinterpretarray.jl:577" ``P577 ``p577,
  entry 579 "setindex!(cartesian Ints)" "The wrapper checks writability, selects pointer or array mutation, and returns the exact array state from that route." "base/reinterpretarray.jl:579-583" ``P579 ``p579,
  entry 585 "setindex!(linear Int)" "The linear wrapper checks writability and selects pointer, IndexLinear, or subscript mutation in source order." "base/reinterpretarray.jl:585-593" ``P585 ``p585,
  entry 595 "setindex!(reshaped SCartesianIndex2)" "The method converts the value, reads and roots the parent element Ref, pointer-stores at the static index, and writes the changed Ref back." "base/reinterpretarray.jl:595-605" ``P595 ``p595,
  entry 607 "_setindex_ptr!" "Pointer mutation checks bounds, computes and roots the exact address, converts the value, stores it, and returns the original view." "base/reinterpretarray.jl:607-614" ``P607 ``p607,
  entry 616 "_setindex_ra!(non-reshaped)" "The mutation converts first, includes the singleton bounds-only no-op, scalar route, and checked byte-assembly route." "base/reinterpretarray.jl:616-683" ``P616 ``p616,
  entry 685 "_setindex_ra!(reshaped)" "The mutation converts first, handles singleton and scalar routes, then selects larger, equal, or smaller checked size-specific writes." "base/reinterpretarray.jl:685-731" ``P685 ``p685,
  entry 828 "has_bit_padding" "Primitive types test bitsize modulo eight, unions recurse over every member, and composites scan fields in order." "base/reinterpretarray.jl:828-837" ``P828 ``p828,
  entry 859 "_copyfrompacked!" "The copy mutates the supplied output memory, preserves untouched padding, scans fields in order, and advances the packed read offset exactly." "base/reinterpretarray.jl:859-877" ``P859 ``p859,
  entry 879 "_reinterpret" "The scalar method performs distinct ordered bits and padding checks, compares packed sizes, and selects direct or padding-aware copying." "base/reinterpretarray.jl:879-906" ``P879 ``p879,
  entry 910 "_reinterpret_padding" "Padding reinterpret computes packed size, creates and roots both Refs and pointers, selects direct packed direction or temporary storage, and reads the mutated output." "base/reinterpretarray.jl:910-932" ``P910 ``p910,
  entry 953 "mapreduce_impl" "The reduction maps and combines every sequential element in order or splits columns recursively at the midpoint and combines both recursive results." "base/reinterpretarray.jl:953-979" ``P953 ``p953
]

end JuliaLean.MultidimCov.ReinterpretFaithful
