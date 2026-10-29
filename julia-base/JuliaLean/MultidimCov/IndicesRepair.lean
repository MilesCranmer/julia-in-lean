import JuliaLean.Core
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.IndicesRepair

open JuliaLean
open JuliaLean.Registry

inductive Error where
  | methodError
  | argument
  | dimensionMismatch (dimension : Option Nat)
  | bounds
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev Result (α : Type) := Except Error α

inductive Style where
  | linear
  | cartesian
  deriving Repr, DecidableEq

inductive ArrayClass where
  | bottom
  | abstractArray
  | array
  | range
  deriving Repr, DecidableEq

def indexStyleType : ArrayClass → Style
  | .bottom | .array | .range => .linear
  | .abstractArray => .cartesian

def indexStyleValue (typeOf : A → ArrayClass) (array : A) : Style :=
  indexStyleType (typeOf array)

def indexStyleBottomSlurp (_arguments : List A) : Result Style := .error .methodError

def combineStyle : Style → Style → Style
  | .linear, .linear => .linear
  | _, _ => .cartesian

theorem combineStyle_linear_iff (left right : Style) :
    combineStyle left right = .linear ↔ left = .linear ∧ right = .linear := by
  cases left <;> cases right <;> simp [combineStyle]

def indexStyleMany (typeOf : A → ArrayClass) : A → List A → Style
  | array, [] => indexStyleValue typeOf array
  | array, next :: rest => combineStyle (indexStyleValue typeOf array)
      (indexStyleMany typeOf next rest)

def IndexStyleContract : Prop :=
  (∀ {A : Type} (typeOf : A → ArrayClass) array,
    indexStyleValue typeOf array = indexStyleType (typeOf array)) ∧
  (∀ {A : Type} (arguments : List A), indexStyleBottomSlurp arguments = .error .methodError) ∧
  indexStyleType .bottom = .linear ∧
  indexStyleType .abstractArray = .cartesian ∧
  indexStyleType .array = .linear ∧
  indexStyleType .range = .linear ∧
  (∀ left right, combineStyle left right = .linear ↔ left = .linear ∧ right = .linear) ∧
  (∀ {A : Type} (typeOf : A → ArrayClass) first rest,
    indexStyleMany typeOf first rest = .linear ↔
      indexStyleValue typeOf first = .linear ∧
        ∀ value ∈ rest, indexStyleValue typeOf value = .linear)

theorem indexStyleContract : IndexStyleContract := by
  unfold IndexStyleContract
  refine ⟨fun _ _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro left right
    cases left <;> cases right <;> simp [combineStyle]
  · intro A typeOf first rest
    induction rest generalizing first with
    | nil => simp [indexStyleMany]
    | cons next rest ih =>
        rw [indexStyleMany, combineStyle_linear_iff, ih]
        simp only [List.mem_cons, forall_eq_or_imp]

inductive ShapeError where
  | mismatch (dimension : Option Nat)
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev ShapeResult (α : Type) := Except ShapeError α

def checkPrefix (equal : A → A → Bool) : List A → List A → Nat → ShapeResult Unit
  | _, [], _ => .ok ()
  | [], _ :: _, dimension => .error (.mismatch (some dimension))
  | a :: as, b :: bs, dimension =>
      if equal a b then checkPrefix equal as bs (dimension + 1)
      else .error (.mismatch (some dimension))

def checkTrailing (isOne : A → Bool) : List A → Nat → ShapeResult Unit
  | [], _ => .ok ()
  | a :: as, dimension =>
      if isOne a then checkTrailing isOne as (dimension + 1)
      else .error (.mismatch (some dimension))

def promoteShapeGe (equal : A → A → Bool) (isOne : A → Bool)
    (long short : List A) : ShapeResult (List A) :=
  match checkPrefix equal long short 1 with
  | .error error => .error error
  | .ok _ => match checkTrailing isOne (long.drop short.length) (short.length + 1) with
    | .error error => .error error
    | .ok _ => .ok long

def promoteShape (equal : A → A → Bool) (isOne : A → Bool)
    (left right : List A) : ShapeResult (List A) :=
  if left.length < right.length then promoteShapeGe equal isOne right left
  else promoteShapeGe equal isOne left right

def normalizeAxes (firstIndex lastIndex : A → ShapeResult I)
    (makeRange : I → I → ShapeResult R) (axes : List A) : ShapeResult (List R) :=
  axes.mapM fun axis => do
    let first ← firstIndex axis
    let last ← lastIndex axis
    makeRange first last

def promoteArrays (axes : A → ShapeResult (List I)) (equal : I → I → Bool)
    (isOne : I → Bool) (left right : A) : ShapeResult (List I) :=
  match axes left with
  | .error error => .error error
  | .ok leftAxes => match axes right with
    | .error error => .error error
    | .ok rightAxes => promoteShape equal isOne leftAxes rightAxes

def shapeMessage (oneTo dims : List A → Bool)
    (lastIndex firstIndex : A → ShapeResult I)
    (makeRange : I → I → ShapeResult R)
    (showAxes : List R → ShapeResult String) (showDims : List I → ShapeResult String)
    (left : List A) (right : Option (List A)) (dimension : Option Nat) : ShapeResult String := do
  let leftLast ← if oneTo left then left.mapM lastIndex else .ok []
  let rightLast ← match right with
    | some values => if oneTo values then values.mapM lastIndex else .ok []
    | none => .ok []
  let hasAxes := !(dims left && match right with | some values => dims values | none => true)
  _ ← if hasAxes then normalizeAxes firstIndex lastIndex makeRange left >>= showAxes
    else showDims leftLast
  _ ← (match right with
    | some values => if hasAxes then normalizeAxes firstIndex lastIndex makeRange values >>= showAxes
      else showDims rightLast
    | none => .ok "")
  .error (.mismatch dimension)

theorem mapM_length {E A B : Type} (function : A → Except E B) :
    ∀ (input : List A) (output : List B), List.mapM function input = Except.ok output →
      output.length = input.length := by
  intro input
  induction input with
  | nil =>
      intro output h
      change Except.ok [] = Except.ok output at h
      exact congrArg List.length (Except.ok.inj h).symm
  | cons first rest ih =>
      intro output h
      cases hf : function first with
      | error error => simp [List.mapM_cons, hf, bind, Except.bind] at h
      | ok value =>
          cases hr : rest.mapM function with
          | error error => simp [List.mapM_cons, hf, hr, bind, Except.bind] at h
          | ok tail =>
              simp [List.mapM_cons, hf, hr, bind, Except.bind, pure, Except.pure] at h
              subst output
              simp [ih tail hr]

def ShapeContract : Prop :=
  (∀ {A : Type} equal isOne (left right result : List A),
    promoteShape equal isOne left right = .ok result →
      (result = left ∨ result = right) ∧ result.length = max left.length right.length) ∧
  (∀ {A I R : Type} firstIndex lastIndex makeRange axes output,
    normalizeAxes (A := A) (I := I) (R := R) firstIndex lastIndex makeRange axes = .ok output →
      output.length = axes.length) ∧
  (∀ {A I : Type} axes equal isOne left right output,
    promoteArrays (A := A) (I := I) axes equal isOne left right = .ok output →
      ∃ leftAxes rightAxes,
        axes left = .ok leftAxes ∧ axes right = .ok rightAxes ∧
        promoteShape equal isOne leftAxes rightAxes = .ok output)

theorem shapeContract : ShapeContract := by
  unfold ShapeContract
  constructor
  · intro A equal isOne left right result h
    unfold promoteShape at h
    split at h
    · have hlen : right.length = max left.length right.length := by omega
      cases hp : checkPrefix equal right left 1 <;>
        cases ht : checkTrailing isOne (right.drop left.length) (left.length + 1) <;>
        simp [promoteShapeGe, hp, ht] at h
      subst result
      exact ⟨Or.inr rfl, hlen⟩
    · have hlen : left.length = max left.length right.length := by omega
      cases hp : checkPrefix equal left right 1 <;>
        cases ht : checkTrailing isOne (left.drop right.length) (right.length + 1) <;>
        simp [promoteShapeGe, hp, ht] at h
      subst result
      exact ⟨Or.inl rfl, hlen⟩
  constructor
  · intro A I R firstIndex lastIndex makeRange axes output h
    unfold normalizeAxes at h
    exact mapM_length _ _ _ h
  · intro A I axes equal isOne left right output h
    cases hl : axes left with
    | error error => simp [promoteArrays, hl] at h
    | ok leftAxes =>
        cases hr : axes right with
        | error error => simp [promoteArrays, hl, hr] at h
        | ok rightAxes =>
            have hs := h
            rw [promoteArrays, hl, hr] at hs
            exact ⟨leftAxes, rightAxes, rfl, rfl, hs⟩

def shapesMatch (equal : A → A → Bool) (isOne : A → Bool) : List A → List A → Bool
  | [], [] => true
  | left, [] => left.all isOne
  | [], right => right.all isOne
  | a :: as, b :: bs => equal a b && shapesMatch equal isOne as bs

def setindexShapeCheck (equal : I → I → Bool) (isOne : I → Bool)
    (lengthX : X → I) (sizeX : X → List I) (product : List I → I)
    (x : X) (shape : List I) : Result Unit :=
  let isMatch := if (sizeX x).length = 1 || shape.length = 1 then
    equal (lengthX x) (product shape)
  else shapesMatch equal isOne (sizeX x) shape
  if isMatch then .ok () else .error (.dimensionMismatch none)

def scalarSetindexShapeCheck (equal : I → I → Bool) (lengthX : X → I)
    (x : X) (count : I) : Result Unit :=
  if equal (lengthX x) count then .ok () else .error (.dimensionMismatch none)

def unsupportedSetindexShape (_value : X) (_shape : List I) : Result Unit := .error .argument

def SetindexContract : Prop :=
  (∀ {A : Type} equal isOne (values : List A),
    shapesMatch equal isOne values [] = values.all isOne ∧
    shapesMatch equal isOne [] values = values.all isOne) ∧
  (∀ {A : Type} (equal : A → A → Bool) (isOne : A → Bool)
      (a b : A) (as bs : List A),
    shapesMatch equal isOne (a :: as) (b :: bs) = true → equal a b = true) ∧
  (∀ {X I : Type} (equal : I → I → Bool) (isOne : I → Bool)
      (lengthX : X → I) (sizeX : X → List I) (product : List I → I)
      (x : X) (shape : List I),
    setindexShapeCheck equal isOne lengthX sizeX product x shape = .ok () ↔
      (if (sizeX x).length = 1 || shape.length = 1 then
        equal (lengthX x) (product shape) else shapesMatch equal isOne (sizeX x) shape) = true) ∧
  (∀ {X I : Type} (value : X) (shape : List I), unsupportedSetindexShape value shape = .error .argument)

theorem setindexContract : SetindexContract := by
  unfold SetindexContract
  constructor
  · intro A equal isOne values
    cases values <;> simp [shapesMatch]
  constructor
  · intro A equal isOne a b as bs h
    simp [shapesMatch] at h
    exact h.1
  constructor
  · intros
    simp [setindexShapeCheck]
  · intros
    rfl

structure IntegerValue where
  value : Int
  fitsInt : Bool
  deriving Repr, DecidableEq

structure BoolArray where
  axes : List (List Int)
  values : List Bool
  deriving Repr, DecidableEq

inductive ConvertedIndex (C A : Type) where
  | integer (value : Int)
  | logical (array : BoolArray)
  | array (value : A)
  | custom (value : C)
  deriving Repr, DecidableEq

def convertInteger (value : IntegerValue) : Result Int :=
  if value.fitsInt then .ok value.value else .error (.callback 1)

def reinterpretUInt64 (value : Nat) : Int := wrapInt .i64 value

def toIndexDefault (convertCustom : C → Result (ConvertedIndex C A))
    (value : C) : Result (ConvertedIndex C A) := convertCustom value

def toIndexInteger (value : IntegerValue) : Result (ConvertedIndex C A) :=
  match convertInteger value with
  | .error error => .error error
  | .ok integer => .ok (.integer integer)

def toIndexBool (_value : Bool) : Result (ConvertedIndex C A) := .error .argument

def toIndexBoolArray (array : BoolArray) : Result (ConvertedIndex C A) := .ok (.logical array)

def toIndexArray (array : A) : Result (ConvertedIndex C A) := .ok (.array array)

def toIndices (convert : C → Result O) : List C → Result (List O)
  | [] => .ok []
  | first :: rest => match convert first with
    | .error error => .error error
    | .ok converted => match toIndices convert rest with
      | .error error => .error error
      | .ok tail => .ok (converted :: tail)

def dropZeroDim : List C → List C
  | [] => []
  | first :: rest => first :: dropZeroDim rest

def IndexConversionContract : Prop :=
  (∀ {C A : Type} (convertCustom : C → Result (ConvertedIndex C A)) (value : C),
    toIndexDefault (C := C) (A := A) convertCustom value = convertCustom value) ∧
  (∀ {C A : Type} (value : IntegerValue) (output : ConvertedIndex C A),
    toIndexInteger (C := C) (A := A) value = .ok output ↔
      value.fitsInt = true ∧ output = .integer value.value) ∧
  (∀ {C A : Type} (value : Bool), toIndexBool (C := C) (A := A) value = .error .argument) ∧
  (∀ {C A : Type} (array : BoolArray), toIndexBoolArray (C := C) (A := A) array = .ok (.logical array)) ∧
  (∀ {C A : Type} (array : A), toIndexArray (C := C) array = .ok (.array array)) ∧
  (∀ value : Nat, reinterpretUInt64 value = wrapInt .i64 value) ∧
  (∀ {C O : Type} (convert : C → Result O) (values : List C) (output : List O),
    toIndices (C := C) (O := O) convert values = .ok output → output.length = values.length) ∧
  (∀ {C : Type} (values : List C), dropZeroDim values = values)

theorem indexConversionContract : IndexConversionContract := by
  unfold IndexConversionContract
  refine ⟨fun _ _ => rfl, ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro C A value output
    cases hfits : value.fitsInt <;> cases output <;>
      simp [toIndexInteger, convertInteger, hfits, eq_comm]
  · intro C O convert values
    induction values with
    | nil => simp [toIndices]
    | cons first rest ih =>
        intro output h
        cases hc : convert first with
        | error error => simp [toIndices, hc] at h
        | ok value =>
            cases ht : toIndices convert rest with
            | error error => simp [toIndices, hc, ht] at h
            | ok tail =>
                simp [toIndices, hc, ht] at h
                subst output
                simp [ih tail ht]
  · intro C values
    induction values <;> simp [dropZeroDim, *]

structure Slice (R : Type) where
  indices : R
  deriving Repr, DecidableEq

def sliceIdentity (slice : Slice R) := slice

def sliceConvert (convert : R → Result T) (slice : Slice R) : Result (Slice T) :=
  match convert slice.indices with
  | .error error => .error error
  | .ok converted => .ok ⟨converted⟩

def sliceAxes1 (identityRange : R → Result AX) (isOneTo : R → Bool)
    (slice : Slice R) : Result AX :=
  if isOneTo slice.indices then identityRange slice.indices else identityRange slice.indices

def sliceFirst (first : R → Result I) (slice : Slice R) := first slice.indices
def sliceLast (last : R → Result I) (slice : Slice R) := last slice.indices
def sliceSize (length : R → Result I) (slice : Slice R) : Result (I × Unit) := do
  .ok (← length slice.indices, ())

def sliceGetindex (checkbounds : Slice R → I → Result Unit)
    (slice : Slice R) (index : I) : Result I :=
  match checkbounds slice index with
  | .error error => .error error
  | .ok _ => .ok index

def sliceIterate (iterate : R → S → Result O) (slice : Slice R) (state : S) :=
  iterate slice.indices state

def SliceContract : Prop :=
  (∀ {R : Type} slice, sliceIdentity (R := R) slice = slice ∧
    sliceIdentity (sliceIdentity slice) = sliceIdentity slice) ∧
  (∀ {R T : Type} convert slice output,
    sliceConvert (R := R) (T := T) convert slice = .ok output →
      ∃ converted, convert slice.indices = .ok converted ∧ output.indices = converted) ∧
  (∀ {R I : Type} checkbounds slice index,
    sliceGetindex (R := R) (I := I) checkbounds slice index = .ok index ↔
      checkbounds slice index = .ok ()) ∧
  (∀ {R S O : Type} iterate slice state,
    sliceIterate (R := R) (S := S) (O := O) iterate slice state = iterate slice.indices state)

theorem sliceContract : SliceContract := by
  unfold SliceContract
  refine ⟨fun _ => ⟨rfl, rfl⟩, ?_, ?_, fun _ _ _ => rfl⟩
  · intro R T convert slice output h
    cases hc : convert slice.indices with
    | error error => simp [sliceConvert, hc] at *
    | ok value =>
        simp [sliceConvert, hc] at h
        subst output
        exact ⟨value, rfl, rfl⟩
  · intro R I checkbounds slice index
    cases hc : checkbounds slice index <;> simp [sliceGetindex, hc]

structure IdentityUnitRange (R : Type) where
  indices : R
  deriving Repr, DecidableEq

def identityRangeIdentity (range : IdentityUnitRange R) := range

def identityRangeConvert (convert : R → Result T)
    (range : IdentityUnitRange R) : Result (IdentityUnitRange T) := do
  .ok ⟨← convert range.indices⟩

def identityAxes1 (isOneTo : R → Bool) (oneToAxis : R → AX)
    (range : IdentityUnitRange R) : Sum (IdentityUnitRange R) AX :=
  if isOneTo range.indices then .inr (oneToAxis range.indices) else .inl range

def identityGetindex (checkbounds : IdentityUnitRange R → I → Result Unit)
    (convert : I → Result O) (range : IdentityUnitRange R) (index : I) : Result O := do
  checkbounds range index
  convert index

def identityRangeGetindex (checkbounds : IdentityUnitRange R → I → Result Unit)
    (convert : I → Result O) (range : IdentityUnitRange R) (index : I) : Result O := do
  checkbounds range index
  convert index

def identityPreservingGetindex (checkbounds : S → I → Result Unit)
    (source : S) (index : I) : Result I :=
  match checkbounds source index with
  | .error error => .error error
  | .ok _ => .ok index

def identityIterate (iterate : R → S → Result O)
    (range : IdentityUnitRange R) (state : S) := iterate range.indices state

def IdentityContract : Prop :=
  (∀ {R : Type} range, identityRangeIdentity (R := R) range = range ∧
    identityRangeIdentity (identityRangeIdentity range) = identityRangeIdentity range) ∧
  (∀ {R I O : Type} checkbounds convert range index,
    identityGetindex (R := R) (I := I) (O := O) checkbounds convert range index =
      identityRangeGetindex checkbounds convert range index) ∧
  (∀ {S I : Type} checkbounds source index,
    identityPreservingGetindex (S := S) (I := I) checkbounds source index = .ok index ↔
      checkbounds source index = .ok ()) ∧
  (∀ {R S O : Type} iterate range state,
    identityIterate (R := R) (S := S) (O := O) iterate range state = iterate range.indices state)

theorem identityContract : IdentityContract := by
  unfold IdentityContract
  refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, ?_, fun _ _ _ => rfl⟩
  intro S I checkbounds source index
  cases hc : checkbounds source index <;> simp [identityPreservingGetindex, hc]

structure LinearIndices (R : Type) where
  indices : List R
  deriving Repr, DecidableEq

def linearConvert (convert : R → Result T) (indices : LinearIndices R) : Result (LinearIndices T) :=
  match indices.indices.mapM convert with
  | .error error => .error error
  | .ok converted => .ok ⟨converted⟩

def convert2indInteger (oneto : IntegerValue → Result R) (value : IntegerValue) := oneto value

def convert2indRange (first last : R → Result I) (makeRange : I → I → Result O)
    (range : R) : Result O :=
  match first range with
  | .error error => .error error
  | .ok firstValue => match last range with
    | .error error => .error error
    | .ok lastValue => makeRange firstValue lastValue

def linearFromMixed (convertInteger : IntegerValue → Result R)
    (convertRange : A → Result R) : List (Sum IntegerValue A) → Result (LinearIndices R)
  | [] => .ok ⟨[]⟩
  | .inl value :: rest => match convertInteger value with
    | .error error => .error error
    | .ok converted => match linearFromMixed convertInteger convertRange rest with
      | .error error => .error error
      | .ok tail => .ok ⟨converted :: tail.indices⟩
  | .inr range :: rest => match convertRange range with
    | .error error => .error error
    | .ok converted => match linearFromMixed convertInteger convertRange rest with
      | .error error => .error error
      | .ok tail => .ok ⟨converted :: tail.indices⟩

def LinearConstructorContract : Prop :=
  (∀ {R T : Type} convert indices output,
    linearConvert (R := R) (T := T) convert indices = .ok output →
      output.indices.length = indices.indices.length) ∧
  (∀ {R I O : Type} first last makeRange range output,
    convert2indRange (R := R) (I := I) (O := O) first last makeRange range = .ok output →
      ∃ firstValue lastValue,
        first range = .ok firstValue ∧ last range = .ok lastValue ∧
        makeRange firstValue lastValue = .ok output) ∧
  (∀ {R A : Type} convertInteger convertRange values output,
    linearFromMixed (R := R) (A := A) convertInteger convertRange values = .ok output →
      output.indices.length = values.length)

theorem linearConstructorContract : LinearConstructorContract := by
  unfold LinearConstructorContract
  constructor
  · intro R T convert indices output h
    cases hm : indices.indices.mapM convert with
    | error error => simp [linearConvert, hm] at h
    | ok mapped =>
        simp [linearConvert, hm] at h
        subst output
        exact mapM_length convert indices.indices mapped hm
  constructor
  · intro R I O first last makeRange range output h
    cases hf : first range with
    | error error => simp [convert2indRange, hf] at h
    | ok firstValue =>
        cases hl : last range with
        | error error => simp [convert2indRange, hf, hl] at h
        | ok lastValue =>
            have hs := h
            rw [convert2indRange, hf, hl] at hs
            exact ⟨firstValue, lastValue, rfl, rfl, hs⟩
  · intro R A convertInteger convertRange values
    induction values with
    | nil => simp [linearFromMixed]
    | cons first rest ih =>
        intro output h
        cases first with
        | inl value =>
            cases hc : convertInteger value with
            | error error => simp [linearFromMixed, hc] at h
            | ok converted =>
                cases ht : linearFromMixed convertInteger convertRange rest with
                | error error => simp [linearFromMixed, hc, ht] at h
                | ok tail =>
                    simp [linearFromMixed, hc, ht] at h
                    subst output
                    simp [ih tail ht]
        | inr range =>
            cases hc : convertRange range with
            | error error => simp [linearFromMixed, hc] at h
            | ok converted =>
                cases ht : linearFromMixed convertInteger convertRange rest with
                | error error => simp [linearFromMixed, hc, ht] at h
                | ok tail =>
                    simp [linearFromMixed, hc, ht] at h
                    subst output
                    simp [ih tail ht]

def promoteLinear (promote : R → R → T) (left right : LinearIndices R) : LinearIndices T :=
  ⟨List.zipWith promote left.indices right.indices⟩

def promoteWrapper (promote : R → R → T) (left right : R) : T := promote left right

def LinearPromotionContract : Prop :=
  (∀ {R T : Type} promote left right,
    (promoteLinear (R := R) (T := T) promote left right).indices.length =
      min left.indices.length right.indices.length) ∧
  (∀ {R T : Type} promote left right,
    promoteWrapper (R := R) (T := T) promote left right = promote left right)

theorem linearPromotionContract : LinearPromotionContract := by
  unfold LinearPromotionContract
  constructor
  · intros
    simp [promoteLinear]
  · intros
    rfl

def linearAxes (axes1 : R → AX) (indices : LinearIndices R) := indices.indices.map axes1
def linearSize (length : R → N) (indices : LinearIndices R) := indices.indices.map length

def linearIsassigned (checkbounds : LinearIndices R → Int → Bool)
    (indices : LinearIndices R) (index : Int) := checkbounds indices index

def linearGetindex (checkbounds : LinearIndices R → I → Result Unit)
    (indices : LinearIndices R) (index : I) : Result I :=
  match checkbounds indices index with
  | .error error => .error error
  | .ok _ => .ok index

def linearRangeGetindex (checkbounds : LinearIndices R → I → Result Unit)
    (vectorIndex : R → I → Result O) (first last : LinearIndices R → Result Int)
    (makeRangeIndex : Int → Int → I → Result O) (indices : LinearIndices R)
    (rankOne : Bool) (index : I) : Result O := do
  checkbounds indices index
  if rankOne then match indices.indices with
    | firstRange :: _ => vectorIndex firstRange index
    | [] => .error .bounds
  else do
    let firstValue ← first indices
    let lastValue ← last indices
    makeRangeIndex firstValue lastValue index

def linearIterateOne (axes1 : R → AX) (iterate : AX → S → Result O)
    (indices : LinearIndices R) (state : S) : Result O :=
  match indices.indices with
  | firstRange :: _ => iterate (axes1 firstRange) state
  | [] => .error .bounds

def linearIterate (length : LinearIndices R → Int)
    (indices : LinearIndices R) (state : Int := 1) : Option (Int × Int) :=
  if state > length indices then none else some (state, state + 1)

def LinearValueContract : Prop :=
  (∀ {R AX : Type} axes1 indices,
    (linearAxes (R := R) (AX := AX) axes1 indices).length = indices.indices.length) ∧
  (∀ {R N : Type} length indices,
    (linearSize (R := R) (N := N) length indices).length = indices.indices.length) ∧
  (∀ {R I : Type} checkbounds indices index,
    linearGetindex (R := R) (I := I) checkbounds indices index = .ok index ↔
      checkbounds indices index = .ok ()) ∧
  (∀ {R : Type} length indices state,
    linearIterate (R := R) length indices state =
      if state > length indices then none else some (state, state + 1)) ∧
  (∀ {R : Type} (indices : LinearIndices R), indices = indices)

theorem linearValueContract : LinearValueContract := by
  unfold LinearValueContract
  refine ⟨?_, ?_, ?_, ?_, fun _ => rfl⟩
  · intros
    simp [linearAxes]
  · intros
    simp [linearSize]
  · intro R I checkbounds indices index
    cases hc : checkbounds indices index <;> simp [linearGetindex, hc]
  · intros
    rfl

private def entry (id : String) (fns : List String) (statement source : String)
    (prop theoremName : Lean.Name) : Entry :=
  { id, juliaFile := "base/indices.jl", juliaFns := fns, statement, source,
    status := .proven, prop, thm := some theoremName }

def entries : List Entry := []

end JuliaLean.MultidimCov.IndicesRepair
