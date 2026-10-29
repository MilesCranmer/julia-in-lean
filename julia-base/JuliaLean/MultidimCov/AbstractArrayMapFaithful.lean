import JuliaLean.MultidimCov.AbstractArrayOrderIndexFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayMapFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful
open AbstractArrayConcatFaithful
open AbstractArrayHvncatFaithful
open AbstractArrayStackFaithful

structure DimensionInput where
  isInteger : Bool
  value : Int
  printed : AnyValue
  deriving Repr, DecidableEq

inductive Selector (Axis Index : Type) where
  | colon
  | scalar (value : Index)
  | slice (axis : Axis)
  deriving Repr, DecidableEq

def validateDimensions (ndims : A → CResult Int) (array : A) : List DimensionInput → CResult Unit
  | [] => .ok ()
  | dimension :: rest =>
      if ¬dimension.isInteger then
        .error (.argument (.literal "mapslices dimension must be an integer"))
      else if dimension.value < 1 then
        .error (.argument (.literal "mapslices dimension must be at least one"))
      else do
        let rank ← ndims array
        if rank < dimension.value then
          .error (.argument (.literal "mapslices does not accept dimensions above ndims"))
        else validateDimensions ndims array rest

def dimensionMask (rank : Int) (dimensions : List DimensionInput) : List Bool :=
  (List.range rank.toNat).map fun index =>
    dimensions.any fun dimension => dimension.value = Int.ofNat index + 1

def firstSliceIndices (firstindex : A → IntegerValue → CResult K)
    (array : A) : List Bool → Int → CResult (List (Selector AX K))
  | [], _ => .ok []
  | selected :: rest, dimension => do
      let head ← if selected then .ok .colon else do
        let index ← firstindex array ⟨dimension⟩
        .ok (.scalar index)
      let tail ← firstSliceIndices firstindex array rest (dimension + 1)
      .ok (head :: tail)

def resultAxes (axesResult : R → IntegerValue → CResult AX)
    (axesInput : A → IntegerValue → CResult AX) (result : R) (array : A) :
    List Bool → Int → Int → CResult (List AX)
  | [], _, _ => .ok []
  | selected :: rest, dimension, resultDimension => do
      let axis ← if selected then axesResult result ⟨resultDimension⟩
        else axesInput array ⟨dimension⟩
      let tail ← resultAxes axesResult axesInput result array rest (dimension + 1)
        (if selected then resultDimension + 1 else resultDimension)
      .ok (axis :: tail)

def sliceResultIndices (axes : A → IntegerValue → CResult AX)
    (firstindex : A → IntegerValue → CResult K) (array : A) :
    List Bool → Int → Bool → CResult (List (Selector AX K))
  | [], _, _ => .ok []
  | selected :: rest, dimension, useSlice => do
      let head ← if selected then do
        let axis ← axes array ⟨dimension⟩
        if useSlice then .ok (.slice axis) else
          let first ← firstindex array ⟨dimension⟩
          .ok (.scalar first)
      else do
        let first ← firstindex array ⟨dimension⟩
        .ok (.scalar first)
      let tail ← sliceResultIndices axes firstindex array rest (dimension + 1) useSlice
      .ok (head :: tail)

/-- `mapslices`, lines 3385-3448. -/
def m3385 (mapWhole : F → A → CResult A) (ndims : A → CResult Int)
    (firstindex : A → IntegerValue → CResult K) (getindex : A → List (Selector AX K) → CResult A)
    (apply : F → A → CResult A) (isArray : A → Bool) (size : A → CResult (List Int))
    (similarScalar : A → A → CResult A) (setFirst : A → A → CResult A)
    (axes : A → IntegerValue → CResult AX) (oneToOne : CResult AX)
    (similarAxes : A → List AX → CResult A)
    (cartesianDrop : A → List AX → CResult I) (concatenate : A → A → List (Selector AX K) → CResult A)
    (isStrided isNumberArray : A → Bool)
    (inner : A → I → F → A → List Bool → A → Bool → CResult A)
    (function : F) (array : A) (dimensions : List DimensionInput) : CResult A :=
  if dimensions.isEmpty then mapWhole function array
  else do
    validateDimensions ndims array dimensions
    let rank ← ndims array
    let mask := dimensionMask rank dimensions
    let initialIndices ← firstSliceIndices firstindex array mask 1
    let slice ← getindex array initialIndices
    let rawResult ← apply function slice
    let result ← if isArray rawResult then do
      let resultRank ← ndims rawResult
      let selectedCount := mask.count true
      if selectedCount < resultRank then
        let resultShape ← size rawResult
        if (resultShape.drop selectedCount).any (1 < ·) then
          .error (.dimensionMismatch (.literal "mapslices cannot assign slice result into output"))
        else .ok rawResult
      else .ok rawResult
    else do
      let boxed ← similarScalar slice rawResult
      setFirst boxed rawResult
    let outputAxes ← resultAxes axes axes result array mask 1 1
    let output ← similarAxes result outputAxes
    let iterationAxes ← (List.range rank.toNat).mapM fun offset =>
      if mask.getD offset false then oneToOne else axes array ⟨Int.ofNat offset + 1⟩
    let indices ← cartesianDrop array iterationAxes
    let resultIndices ← sliceResultIndices axes firstindex output mask 1 true
    let initialized ← concatenate output result resultIndices
    let safe := isStrided slice && isNumberArray rawResult
    inner initialized indices function array mask slice safe
def P3385 : Prop := ∀ {F A K AX I : Type} (mapWhole : F → A → CResult A)
    (ndims : A → CResult Int) (firstindex : A → IntegerValue → CResult K)
    (getindex : A → List (Selector AX K) → CResult A) (apply : F → A → CResult A)
    (isArray : A → Bool) (size : A → CResult (List Int))
    (similarScalar setFirst : A → A → CResult A) (axes : A → IntegerValue → CResult AX)
    (oneToOne : CResult AX) (similarAxes : A → List AX → CResult A)
    (cartesianDrop : A → List AX → CResult I)
    (concatenate : A → A → List (Selector AX K) → CResult A)
    (isStrided isNumberArray : A → Bool)
    (inner : A → I → F → A → List Bool → A → Bool → CResult A)
    function array dimensions,
  m3385 mapWhole ndims firstindex getindex apply isArray size similarScalar setFirst axes oneToOne
    similarAxes cartesianDrop concatenate isStrided isNumberArray inner function array dimensions =
    if dimensions.isEmpty then mapWhole function array
    else do
      validateDimensions ndims array dimensions
      let rank ← ndims array
      let mask := dimensionMask rank dimensions
      let initialIndices ← firstSliceIndices firstindex array mask 1
      let slice ← getindex array initialIndices
      let rawResult ← apply function slice
      let result ← if isArray rawResult then do
        let resultRank ← ndims rawResult
        let selectedCount := mask.count true
        if selectedCount < resultRank then
          let resultShape ← size rawResult
          if (resultShape.drop selectedCount).any (1 < ·) then
            .error (.dimensionMismatch (.literal "mapslices cannot assign slice result into output"))
          else .ok rawResult
        else .ok rawResult
      else do
        let boxed ← similarScalar slice rawResult
        setFirst boxed rawResult
      let outputAxes ← resultAxes axes axes result array mask 1 1
      let output ← similarAxes result outputAxes
      let iterationAxes ← (List.range rank.toNat).mapM fun offset =>
        if mask.getD offset false then oneToOne else axes array ⟨Int.ofNat offset + 1⟩
      let indices ← cartesianDrop array iterationAxes
      let resultIndices ← sliceResultIndices axes firstindex output mask 1 true
      let initialized ← concatenate output result resultIndices
      let safe := isStrided slice && isNumberArray rawResult
      inner initialized indices function array mask slice safe
theorem p3385 : P3385 := by unfold P3385; intros; rfl

def chooseIndices (axes : A → IntegerValue → StackOutcome AX)
    (coordinates : List K) (array : A) : List Bool → Int → Bool → StackOutcome (List (Selector AX K))
  | [], _, _ => .returned []
  | selected :: rest, dimension, useSlice => do
      let head ← if selected && useSlice then .slice <$> axes array ⟨dimension⟩
        else match coordinates[(dimension - 1).toNat]? with
          | some value => .returned (.scalar value)
          | none => .thrown .bounds
      let tail ← chooseIndices axes coordinates array rest (dimension + 1) useSlice
      .returned (head :: tail)

def mapslicesInnerLoop (axes : A → IntegerValue → StackOutcome AX)
    (unsafeGetSlice : S → A → List (Selector AX K) → StackOutcome S)
    (apply : F → S → StackOutcome R) (isArray : R → Bool)
    (assign : O → List (Selector AX K) → R → StackOutcome O)
    (getindex : A → List (Selector AX K) → StackOutcome S)
    (concatenate : O → R → List (Selector AX K) → StackOutcome O)
    (function : F) (array : A) (mask : List Bool) (safe mustExtend : Bool) :
    O → S → List (List K) → StackOutcome (O × S)
  | output, slice, [] => .returned (output, slice)
  | output, slice, coordinate :: rest =>
      if safe then do
        let sourceIndices ← chooseIndices axes coordinate array mask 1 true
        let nextSlice ← unsafeGetSlice slice array sourceIndices
        let result ← apply function nextSlice
        let outputIndices ← chooseIndices axes coordinate array mask 1 (isArray result || mustExtend)
        let nextOutput ← assign output outputIndices result
        mapslicesInnerLoop axes unsafeGetSlice apply isArray assign getindex concatenate
          function array mask safe mustExtend nextOutput nextSlice rest
      else do
        let sourceIndices ← chooseIndices axes coordinate array mask 1 true
        let freshSlice ← getindex array sourceIndices
        let result ← apply function freshSlice
        let outputIndices ← chooseIndices axes coordinate array mask 1 true
        let nextOutput ← concatenate output result outputIndices
        mapslicesInnerLoop axes unsafeGetSlice apply isArray assign getindex concatenate
          function array mask safe mustExtend nextOutput slice rest

/-- `_inner_mapslices!`, lines 3450-3476. -/
def m3450 (size : O → StackOutcome (List Int)) (axes : A → IntegerValue → StackOutcome AX)
    (unsafeGetSlice : S → A → List (Selector AX K) → StackOutcome S)
    (apply : F → S → StackOutcome R) (isArray : R → Bool)
    (assign : O → List (Selector AX K) → R → StackOutcome O)
    (getindex : A → List (Selector AX K) → StackOutcome S)
    (concatenate : O → R → List (Selector AX K) → StackOutcome O)
    (iterate : I → StackOutcome (IterationRun (List K)))
    (output : O) (indices : I) (function : F) (array : A) (mask : List Bool)
    (slice : S) (safe : Bool) : StackOutcome O := do
  let shape ← size output
  let mustExtend := (mask.zip shape).any fun pair => pair.1 && 1 < pair.2
  let run ← iterate indices
  let result ← mapslicesInnerLoop axes unsafeGetSlice apply isArray assign getindex concatenate
    function array mask safe mustExtend output slice run.values
  match run.terminal with
  | .done => .returned result.1
  | .failed failure => .thrown failure
  | .diverges => .diverged
def P3450 : Prop := ∀ {O A AX S K F R I : Type} (size : O → StackOutcome (List Int))
    (axes : A → IntegerValue → StackOutcome AX)
    (unsafeGetSlice : S → A → List (Selector AX K) → StackOutcome S)
    (apply : F → S → StackOutcome R) (isArray : R → Bool)
    (assign : O → List (Selector AX K) → R → StackOutcome O)
    (getindex : A → List (Selector AX K) → StackOutcome S)
    (concatenate : O → R → List (Selector AX K) → StackOutcome O)
    (iterate : I → StackOutcome (IterationRun (List K)))
    output indices function array mask slice safe,
  m3450 size axes unsafeGetSlice apply isArray assign getindex concatenate iterate output indices
    function array mask slice safe = do
      let shape ← size output
      let mustExtend := (mask.zip shape).any fun pair => pair.1 && 1 < pair.2
      let run ← iterate indices
      let result ← mapslicesInnerLoop axes unsafeGetSlice apply isArray assign getindex concatenate
        function array mask safe mustExtend output slice run.values
      match run.terminal with
      | .done => .returned result.1
      | .failed failure => .thrown failure
      | .diverges => .diverged
theorem p3450 : P3450 := by unfold P3450; intros; rfl

def unaryMapLoop (read : A → K → StackOutcome V) (apply : F → V → StackOutcome W)
    (write : D → K → W → StackOutcome D) (function : F) (source : A) :
    D → List (K × K) → StackOutcome D
  | dest, [] => .returned dest
  | dest, (destinationIndex, sourceIndex) :: rest => do
      let value ← read source sourceIndex
      let mapped ← apply function value
      let next ← write dest destinationIndex mapped
      unaryMapLoop read apply write function source next rest

/-- Unary `map!`, lines 3482-3489. -/
def m3482 (zipIndices : D → A → StackOutcome (IterationRun (K × K)))
    (read : A → K → StackOutcome V) (apply : F → V → StackOutcome W)
    (write : D → K → W → StackOutcome D) (function : F) (dest : D) (source : A) : StackOutcome D := do
  let run ← zipIndices dest source
  let result ← unaryMapLoop read apply write function source dest run.values
  match run.terminal with
  | .done => .returned result
  | .failed failure => .thrown failure
  | .diverges => .diverged
def P3482 : Prop := ∀ {D A K V W F : Type}
    (zipIndices : D → A → StackOutcome (IterationRun (K × K)))
    (read : A → K → StackOutcome V) (apply : F → V → StackOutcome W)
    (write : D → K → W → StackOutcome D) function dest source,
  m3482 zipIndices read apply write function dest source = do
    let run ← zipIndices dest source
    let result ← unaryMapLoop read apply write function source dest run.values
    match run.terminal with
    | .done => .returned result
    | .failed failure => .thrown failure
    | .diverges => .diverged
theorem p3482 : P3482 := by unfold P3482; intros; rfl

def collectMapped (iterate : A → StackOutcome (IterationRun (K × V)))
    (apply : F → V → StackOutcome W) (allocate : A → StackOutcome O)
    (write : O → K → W → StackOutcome O) (function : F) (source : A) : StackOutcome O := do
  let output ← allocate source
  let run ← iterate source
  let result ← run.values.foldlM (fun dest pair => do
    let mapped ← apply function pair.2
    write dest pair.1 mapped) output
  match run.terminal with
  | .done => .returned result
  | .failed failure => .thrown failure
  | .diverges => .diverged

/-- Array `map`, line 3491. -/
def m3491 := @collectMapped
def P3491 : Prop := ∀ {A K V W O F : Type}
    (iterate : A → StackOutcome (IterationRun (K × V)))
    (apply : F → V → StackOutcome W) (allocate : A → StackOutcome O)
    (write : O → K → W → StackOutcome O) function source,
  m3491 iterate apply allocate write function source =
  collectMapped iterate apply allocate write function source
theorem p3491 : P3491 := by unfold P3491; intros; rfl

/-- Array `mapany`, line 3493. -/
def m3493 (length : A → StackOutcome Int) (allocateAny : Int → StackOutcome D)
    (mapBang : F → D → A → StackOutcome D) (function : F) (source : A) : StackOutcome D := do
  let count ← length source
  let dest ← allocateAny count
  mapBang function dest source
def P3493 : Prop := ∀ {A D F : Type} (length : A → StackOutcome Int)
    (allocateAny : Int → StackOutcome D) (mapBang : F → D → A → StackOutcome D)
    function source,
  m3493 length allocateAny mapBang function source = do
    let count ← length source
    let dest ← allocateAny count
    mapBang function dest source
theorem p3493 : P3493 := by unfold P3493; intros; rfl

def mapIteratorValues (apply : F → V → StackOutcome W) (function : F) :
    List V → StackOutcome (List W)
  | [] => .returned []
  | value :: rest => do
      let mapped ← apply function value
      let tail ← mapIteratorValues apply function rest
      .returned (mapped :: tail)

/-- Generic `mapany`, line 3494. -/
def m3494 (iterate : I → StackOutcome (IterationRun V))
    (apply : F → V → StackOutcome W) (function : F) (iterator : I) : StackOutcome (List W) := do
  let run ← iterate iterator
  let values ← mapIteratorValues apply function run.values
  match run.terminal with
  | .done => .returned values
  | .failed failure => .thrown failure
  | .diverges => .diverged
def P3494 : Prop := ∀ {I V W F : Type} (iterate : I → StackOutcome (IterationRun V))
    (apply : F → V → StackOutcome W) function iterator,
  m3494 iterate apply function iterator = do
    let run ← iterate iterator
    let values ← mapIteratorValues apply function run.values
    match run.terminal with
    | .done => .returned values
    | .failed failure => .thrown failure
    | .diverges => .diverged
theorem p3494 : P3494 := by unfold P3494; intros; rfl

/-- Generic `map`, line 3521. `collect` receives the Generator itself so its
allocation and widening semantics remain observable. -/
def m3521 (generator : F → I → G) (collect : G → StackOutcome O)
    (function : F) (iterator : I) : StackOutcome O :=
  collect (generator function iterator)
def P3521 : Prop := ∀ {F I G O : Type} (generator : F → I → G)
    (collect : G → StackOutcome O) function iterator,
  m3521 generator collect function iterator = collect (generator function iterator)
theorem p3521 : P3521 := by unfold P3521; intros; rfl

def m3523 : CResult A := .error (.errorException "map is not defined on dictionaries")
def P3523 : Prop := ∀ (A : Type), (m3523 : CResult A) = .error (.errorException "map is not defined on dictionaries")
theorem p3523 : P3523 := by unfold P3523; intros; rfl
def m3524 : CResult A := .error (.errorException "map is not defined on sets")
def P3524 : Prop := ∀ (A : Type), (m3524 : CResult A) = .error (.errorException "map is not defined on sets")
theorem p3524 : P3524 := by unfold P3524; intros; rfl

def binaryMapLoop (readA : A → KA → StackOutcome VA) (readB : B → KB → StackOutcome VB)
    (apply : F → VA → VB → StackOutcome W) (write : D → KD → W → StackOutcome D)
    (function : F) (left : A) (right : B) : D → List (KD × KA × KB) → StackOutcome D
  | dest, [] => .returned dest
  | dest, (di, ai, bi) :: rest => do
      let a ← readA left ai
      let b ← readB right bi
      let mapped ← apply function a b
      let next ← write dest di mapped
      binaryMapLoop readA readB apply write function left right next rest

/-- Binary `map!`, lines 3527-3536. -/
def m3527 (zipIndices : D → A → B → StackOutcome (IterationRun (KD × KA × KB)))
    (readA : A → KA → StackOutcome VA) (readB : B → KB → StackOutcome VB)
    (apply : F → VA → VB → StackOutcome W) (write : D → KD → W → StackOutcome D)
    (function : F) (dest : D) (left : A) (right : B) : StackOutcome D := do
  let run ← zipIndices dest left right
  let result ← binaryMapLoop readA readB apply write function left right dest run.values
  match run.terminal with
  | .done => .returned result
  | .failed failure => .thrown failure
  | .diverges => .diverged
def P3527 : Prop := ∀ {D A B KD KA KB VA VB W F : Type}
    (zipIndices : D → A → B → StackOutcome (IterationRun (KD × KA × KB)))
    (readA : A → KA → StackOutcome VA) (readB : B → KB → StackOutcome VB)
    (apply : F → VA → VB → StackOutcome W) (write : D → KD → W → StackOutcome D)
    function dest left right,
  m3527 zipIndices readA readB apply write function dest left right = do
    let run ← zipIndices dest left right
    let result ← binaryMapLoop readA readB apply write function left right dest run.values
    match run.terminal with
    | .done => .returned result
    | .failed failure => .thrown failure
    | .diverges => .diverged
theorem p3527 : P3527 := by unfold P3527; intros; rfl

def m3538 (_index : K) : List V := []
def P3538 : Prop := ∀ {K V : Type} (index : K), (m3538 (V := V) index) = []
theorem p3538 : P3538 := by unfold P3538; intros; rfl

def m3539 (getArray : List A → Int → StackOutcome A) (getValue : A → K → StackOutcome V)
    (recursive : K → List A → StackOutcome (List V)) (index : K) (arrays : List A) : StackOutcome (List V) := do
  let first ← getArray arrays 1
  let value ← getValue first index
  let rest ← match arrays with | [] => .thrown .bounds | _ :: tail => recursive index tail
  .returned (value :: rest)
def P3539 : Prop := ∀ {A K V : Type} (getArray : List A → Int → StackOutcome A)
    (getValue : A → K → StackOutcome V)
    (recursive : K → List A → StackOutcome (List V)) index arrays,
  m3539 getArray getValue recursive index arrays = do
    let first ← getArray arrays 1
    let value ← getValue first index
    let rest ← match arrays with | [] => .thrown .bounds | _ :: tail => recursive index tail
    .returned (value :: rest)
theorem p3539 : P3539 := by unfold P3539; intros; rfl

def mapNLinear (iterate : L → StackOutcome (IterationRun K))
    (ithAll : K → List A → StackOutcome (List V)) (apply : F → List V → StackOutcome W)
    (set : D → K → W → StackOutcome D) (function : F) (arrays : List A)
    (dest : D) (indices : L) : StackOutcome D := do
  let run ← iterate indices
  let result ← run.values.foldlM (fun output index => do
    let values ← ithAll index arrays
    let mapped ← apply function values
    set output index mapped) dest
  match run.terminal with
  | .done => .returned result
  | .failed failure => .thrown failure
  | .diverges => .diverged

def mapNCartesian (iterate : D → List A → StackOutcome (IterationRun (K × List K)))
    (getArray : List A → Int → StackOutcome A) (getValue : A → K → StackOutcome V)
    (apply : F → List V → StackOutcome W) (set : D → K → W → StackOutcome D)
    (function : F) (dest : D) (arrays : List A) : StackOutcome D := do
  let run ← iterate dest arrays
  let result ← run.values.foldlM (fun output pair => do
    let values ← (List.range arrays.length).mapM fun offset => do
      let array ← getArray arrays (Int.ofNat offset + 1)
      let index ← match pair.2[offset]? with | some value => .returned value | none => .thrown .bounds
      getValue array index
    let mapped ← apply function values
    set output pair.1 mapped) dest
  match run.terminal with
  | .done => .returned result
  | .failed failure => .thrown failure
  | .diverges => .diverged

def allLinearIndices (linearIndices : A → StackOutcome L)
    (equal : L → L → StackOutcome Bool) (destIndices : L) :
    List A → StackOutcome Bool
  | [] => .returned true
  | array :: rest => do
      if ← equal (← linearIndices array) destIndices then
        allLinearIndices linearIndices equal destIndices rest
      else .returned false

/-- `map_n!`, lines 3544-3591. -/
def m3544 (linearIndicesDest : D → StackOutcome L) (linearIndices : A → StackOutcome L)
    (equal : L → L → StackOutcome Bool) (linear : L → StackOutcome (IterationRun K))
    (ithAll : K → List A → StackOutcome (List V))
    (cartesian : D → List A → StackOutcome (IterationRun (K × List K)))
    (getArray : List A → Int → StackOutcome A) (getValue : A → K → StackOutcome V)
    (apply : F → List V → StackOutcome W) (set : D → K → W → StackOutcome D)
    (function : F) (dest : D) (arrays : List A) : StackOutcome D := do
  let destIndices ← linearIndicesDest dest
  if ← allLinearIndices linearIndices equal destIndices arrays then
    mapNLinear linear ithAll apply set function arrays dest destIndices
  else mapNCartesian cartesian getArray getValue apply set function dest arrays
def P3544 : Prop := ∀ {D A L K V W F : Type}
    (linearIndicesDest : D → StackOutcome L) (linearIndices : A → StackOutcome L)
    (equal : L → L → StackOutcome Bool) (linear : L → StackOutcome (IterationRun K))
    (ithAll : K → List A → StackOutcome (List V))
    (cartesian : D → List A → StackOutcome (IterationRun (K × List K)))
    (getArray : List A → Int → StackOutcome A) (getValue : A → K → StackOutcome V)
    (apply : F → List V → StackOutcome W) (set : D → K → W → StackOutcome D)
    function dest arrays,
  m3544 linearIndicesDest linearIndices equal linear ithAll cartesian getArray getValue apply set
    function dest arrays = do
      let destIndices ← linearIndicesDest dest
      if ← allLinearIndices linearIndices equal destIndices arrays then
        mapNLinear linear ithAll apply set function arrays dest destIndices
      else mapNCartesian cartesian getArray getValue apply set function dest arrays
theorem p3544 : P3544 := by unfold P3544; intros; rfl

/-- Vararg `map!`, lines 3593-3596. -/
def m3593 (mapN : F → D → List A → CResult D) (function : F) (dest : D)
    (arrays : List A) : CResult D :=
  if arrays.isEmpty then .error (.assertion "should dispatch to map!(f, A)")
  else mapN function dest arrays
def P3593 : Prop := ∀ {F D A : Type} (mapN : F → D → List A → CResult D)
    function dest arrays,
  m3593 mapN function dest arrays = if arrays.isEmpty then
    .error (.assertion "should dispatch to map!(f, A)") else mapN function dest arrays
theorem p3593 : P3593 := by unfold P3593; intros; rfl

/-- Multi-input `map`, line 3645. The Generator retains shortest-iterator
semantics; `collect` retains allocation and widening behavior. -/
def m3645 (generator : F → I → List I → G) (collect : G → StackOutcome O)
    (function : F) (first : I) (rest : List I) : StackOutcome O :=
  collect (generator function first rest)
def P3645 : Prop := ∀ {F I G O : Type} (generator : F → I → List I → G)
    (collect : G → StackOutcome O) function first rest,
  m3645 generator collect function first rest = collect (generator function first rest)
theorem p3645 : P3645 := by unfold P3645; intros; rfl

inductive Mutation (A : Type) where
  | success (state : A)
  | failure (state : A) (error : CatFailure)
  | diverged (state : A)
  deriving Repr, DecidableEq

def continueMutation (result : Mutation A) (next : A → Mutation A) : Mutation A :=
  match result with
  | .success state => next state
  | .failure state error => .failure state error
  | .diverged state => .diverged state

def liftMutation (state : A) : CResult B → (B → Mutation A) → Mutation A
  | .ok value, next => next value
  | .error error, _ => .failure state error

/-- Generic converted `push!`, lines 3649-3657. -/
def m3649 (convert : X → CResult V) (length : A → CResult Int)
    (add : Int → Int → CResult Int) (resize : A → Int → Mutation A)
    (lastindex : A → CResult K) (set : A → K → V → Mutation A)
    (array : A) (item : X) : Mutation A :=
  liftMutation array (convert item) fun converted =>
  liftMutation array (length array) fun oldLength =>
  liftMutation array (add oldLength 1) fun newLength =>
  continueMutation (resize array newLength) fun resized =>
  liftMutation resized (lastindex resized) fun index => set resized index converted
def P3649 : Prop := ∀ {X V A K : Type} (convert : X → CResult V)
    (length : A → CResult Int) (add : Int → Int → CResult Int)
    (resize : A → Int → Mutation A) (lastindex : A → CResult K)
    (set : A → K → V → Mutation A) array item,
  m3649 convert length add resize lastindex set array item =
    liftMutation array (convert item) fun converted =>
    liftMutation array (length array) fun oldLength =>
    liftMutation array (add oldLength 1) fun newLength =>
    continueMutation (resize array newLength) fun resized =>
    liftMutation resized (lastindex resized) fun index => set resized index converted
theorem p3649 : P3649 := by unfold P3649; intros; rfl

/-- Any-vector single `push!`, lines 3659-3663. -/
def m3659 (length : A → CResult Int) (add : Int → Int → CResult Int)
    (resize : A → Int → Mutation A) (lastindex : A → CResult K)
    (set : A → K → X → Mutation A) (array : A) (item : X) : Mutation A :=
  liftMutation array (length array) fun oldLength =>
  liftMutation array (add oldLength 1) fun newLength =>
  continueMutation (resize array newLength) fun resized =>
  liftMutation resized (lastindex resized) fun index => set resized index item
def P3659 : Prop := ∀ {A K X : Type} (length : A → CResult Int)
    (add : Int → Int → CResult Int) (resize : A → Int → Mutation A)
    (lastindex : A → CResult K) (set : A → K → X → Mutation A) array item,
  m3659 length add resize lastindex set array item =
    liftMutation array (length array) fun oldLength =>
    liftMutation array (add oldLength 1) fun newLength =>
    continueMutation (resize array newLength) fun resized =>
    liftMutation resized (lastindex resized) fun index => set resized index item
theorem p3659 : P3659 := by unfold P3659; intros; rfl

def pushManyLoop (get : X → Int → CResult V) (addIndex : K → Int → CResult K)
    (set : A → K → V → Mutation A) (items : X) (base : K) :
    A → Int → Nat → Mutation A
  | array, _, 0 => .success array
  | array, index, remaining + 1 =>
      liftMutation array (get items index) fun value =>
      liftMutation array (addIndex base index) fun destination =>
      continueMutation (set array destination value) fun next =>
      pushManyLoop get addIndex set items base next (index + 1) remaining

/-- Any-vector vararg `push!`, lines 3665-3675. -/
def m3665 (lengthA : A → CResult Int) (lengthX : X → CResult Int)
    (add : Int → Int → CResult Int) (resize : A → Int → Mutation A)
    (lastindex : A → CResult K) (subtract : K → Int → CResult K)
    (get : X → Int → CResult V) (addIndex : K → Int → CResult K)
    (set : A → K → V → Mutation A) (array : A) (items : X) : Mutation A :=
  liftMutation array (lengthA array) fun oldLength =>
  liftMutation array (lengthX items) fun count =>
  liftMutation array (add oldLength count) fun newLength =>
  continueMutation (resize array newLength) fun resized =>
  liftMutation resized (lastindex resized) fun last =>
  liftMutation resized (subtract last count) fun base =>
  pushManyLoop get addIndex set items base resized 1 count.toNat
def P3665 : Prop := ∀ {A X K V : Type} (lengthA : A → CResult Int)
    (lengthX : X → CResult Int) (add : Int → Int → CResult Int)
    (resize : A → Int → Mutation A) (lastindex : A → CResult K)
    (subtract : K → Int → CResult K) (get : X → Int → CResult V)
    (addIndex : K → Int → CResult K) (set : A → K → V → Mutation A) array items,
  m3665 lengthA lengthX add resize lastindex subtract get addIndex set array items =
    liftMutation array (lengthA array) fun oldLength =>
    liftMutation array (lengthX items) fun count =>
    liftMutation array (add oldLength count) fun newLength =>
    continueMutation (resize array newLength) fun resized =>
    liftMutation resized (lastindex resized) fun last =>
    liftMutation resized (subtract last count) fun base =>
    pushManyLoop get addIndex set items base resized 1 count.toNat
theorem p3665 : P3665 := by unfold P3665; intros; rfl

def foldPushOutcome (push : A → V → StackOutcome A) : A → List V → StackOutcome A
  | array, [] => .returned array
  | array, value :: rest => do
      let next ← push array value
      foldPushOutcome push next rest

/-- `rest(AbstractArray,state...)`, lines 3688-3695. -/
def m3688 (allocate : StackOutcome A) (length : S → StackOutcome Int)
    (sizehint : A → Int → StackOutcome A)
    (restIterator : S → StateArg → StackOutcome (IterationRun V))
    (push : A → V → StackOutcome A) (source : S) (state : StateArg) : StackOutcome A := do
  let empty ← allocate
  let count ← length source
  let hinted ← sizehint empty count
  let run ← restIterator source state
  let result ← foldPushOutcome push hinted run.values
  match run.terminal with
  | .done => .returned result
  | .failed error => .thrown error
  | .diverges => .diverged
def P3688 : Prop := ∀ {A S StateArg V : Type} (allocate : StackOutcome A)
    (length : S → StackOutcome Int) (sizehint : A → Int → StackOutcome A)
    (restIterator : S → StateArg → StackOutcome (IterationRun V))
    (push : A → V → StackOutcome A) source state,
  m3688 allocate length sizehint restIterator push source state = do
    let empty ← allocate
    let count ← length source
    let hinted ← sizehint empty count
    let run ← restIterator source state
    let result ← foldPushOutcome push hinted run.values
    match run.terminal with
    | .done => .returned result
    | .failed error => .thrown error
    | .diverges => .diverged
theorem p3688 : P3688 := by unfold P3688; intros; rfl

structure KeepState (A K : Type) where
  array : A
  destination : K
  previous : Option K

def keepIndicesLoop (less equal : K → K → CResult Bool) (get : A → K → CResult V)
    (set : A → K → V → Mutation A) (nextind : A → K → CResult K) :
    KeepState A K → List K → Mutation (KeepState A K)
  | state, [] => .success state
  | state, index :: rest =>
      let ordered := match state.previous with
        | none => .ok true
        | some previous => less previous index
      liftMutation state ordered fun valid =>
      if !valid then .failure state (.argument (.literal "indices must be unique and sorted"))
      else liftMutation state (get state.array index) fun value =>
        liftMutation state (equal state.destination index) fun same =>
        let afterSet := if same then Mutation.success state.array
          else set state.array state.destination value
        match afterSet with
        | .failure array error => .failure { state with array } error
        | .diverged array => .diverged { state with array }
        | .success array =>
            let updated : KeepState A K := { state with array, previous := some index }
            liftMutation updated (nextind array state.destination) fun next =>
            keepIndicesLoop less equal get set nextind { updated with destination := next } rest

/-- Index-list `_keepat!`, lines 3699-3715. -/
def m3699 (firstindex : A → CResult K) (iterate : I → StackOutcome (IterationRun K))
    (less equal : K → K → CResult Bool) (get : A → K → CResult V)
    (set : A → K → V → Mutation A) (nextind : A → K → CResult K)
    (lastindex : A → CResult K) (deleteRange : A → K → K → Mutation A)
    (array : A) (indices : I) : Mutation A :=
  liftMutation array (firstindex array) fun first =>
  match iterate indices with
  | .thrown error => .failure array error
  | .diverged => .diverged array
  | .returned run =>
      let initial : KeepState A K := ⟨array, first, none⟩
      match keepIndicesLoop less equal get set nextind initial run.values with
      | .failure state error => .failure state.array error
      | .diverged state => .diverged state.array
      | .success state => match run.terminal with
        | .failed error => .failure state.array error
        | .diverges => .diverged state.array
        | .done => liftMutation state.array (lastindex state.array) fun last =>
          deleteRange state.array state.destination last
def P3699 : Prop := ∀ {A K I V : Type} (firstindex : A → CResult K)
    (iterate : I → StackOutcome (IterationRun K)) (less equal : K → K → CResult Bool)
    (get : A → K → CResult V) (set : A → K → V → Mutation A)
    (nextind : A → K → CResult K) (lastindex : A → CResult K)
    (deleteRange : A → K → K → Mutation A) array indices,
  m3699 firstindex iterate less equal get set nextind lastindex deleteRange array indices =
    liftMutation array (firstindex array) fun first =>
    match iterate indices with
    | .thrown error => .failure array error
    | .diverged => .diverged array
    | .returned run =>
        let initial : KeepState A K := ⟨array, first, none⟩
        match keepIndicesLoop less equal get set nextind initial run.values with
        | .failure state error => .failure state.array error
        | .diverged state => .diverged state.array
        | .success state => match run.terminal with
          | .failed error => .failure state.array error
          | .diverges => .diverged state.array
          | .done => liftMutation state.array (lastindex state.array) fun last =>
            deleteRange state.array state.destination last
theorem p3699 : P3699 := by unfold P3699; intros; rfl

structure MaskState (A K : Type) where
  array : A
  destination : K

def keepMaskLoop (getMask : M → K → CResult Bool) (get : A → K → CResult V)
    (equal : K → K → CResult Bool) (set : A → K → V → Mutation A)
    (nextind : A → K → CResult K) (mask : M) :
    MaskState A K → List K → Mutation (MaskState A K)
  | state, [] => .success state
  | state, index :: rest =>
      liftMutation state (getMask mask index) fun keep =>
      if ¬keep then keepMaskLoop getMask get equal set nextind mask state rest
      else liftMutation state (equal index state.destination) fun same =>
        let copied := if same then Mutation.success state.array else
          liftMutation state.array (get state.array index) fun value => set state.array state.destination value
        match copied with
        | .failure array error => .failure ⟨array, state.destination⟩ error
        | .diverged array => .diverged ⟨array, state.destination⟩
        | .success array =>
            let updated : MaskState A K := ⟨array, state.destination⟩
            liftMutation updated (nextind array state.destination) fun next =>
            keepMaskLoop getMask get equal set nextind mask { updated with destination := next } rest

/-- Boolean-mask `_keepat!`, lines 3717-3731. -/
def m3717 (lengthA : A → CResult Int) (lengthM : M → CResult Int)
    (firstindex : A → CResult K) (eachindex : A → M → StackOutcome (IterationRun K))
    (getMask : M → K → CResult Bool) (get : A → K → CResult V)
    (equal : K → K → CResult Bool) (set : A → K → V → Mutation A)
    (nextind : A → K → CResult K) (lastindex : A → CResult K)
    (deleteRange : A → K → K → Mutation A) (array : A) (mask : M) : Mutation A :=
  liftMutation array (lengthM mask) fun maskLength =>
  liftMutation array (lengthA array) fun arrayLength =>
  if maskLength != arrayLength then .failure array .bounds
  else liftMutation array (firstindex array) fun first =>
    match eachindex array mask with
    | .thrown error => .failure array error
    | .diverged => .diverged array
    | .returned run =>
        let initial : MaskState A K := ⟨array, first⟩
        match keepMaskLoop getMask get equal set nextind mask initial run.values with
        | .failure state error => .failure state.array error
        | .diverged state => .diverged state.array
        | .success state => match run.terminal with
          | .failed error => .failure state.array error
          | .diverges => .diverged state.array
          | .done => liftMutation state.array (lastindex state.array) fun last =>
            deleteRange state.array state.destination last
def P3717 : Prop := ∀ {A M K V : Type} (lengthA : A → CResult Int)
    (lengthM : M → CResult Int) (firstindex : A → CResult K)
    (eachindex : A → M → StackOutcome (IterationRun K))
    (getMask : M → K → CResult Bool) (get : A → K → CResult V)
    (equal : K → K → CResult Bool) (set : A → K → V → Mutation A)
    (nextind : A → K → CResult K) (lastindex : A → CResult K)
    (deleteRange : A → K → K → Mutation A) array mask,
  m3717 lengthA lengthM firstindex eachindex getMask get equal set nextind lastindex deleteRange
    array mask =
    liftMutation array (lengthM mask) fun maskLength =>
    liftMutation array (lengthA array) fun arrayLength =>
    if maskLength != arrayLength then .failure array .bounds
    else liftMutation array (firstindex array) fun first =>
      match eachindex array mask with
      | .thrown error => .failure array error
      | .diverged => .diverged array
      | .returned run =>
          let initial : MaskState A K := ⟨array, first⟩
          match keepMaskLoop getMask get equal set nextind mask initial run.values with
          | .failure state error => .failure state.array error
          | .diverged state => .diverged state.array
          | .success state => match run.terminal with
            | .failed error => .failure state.array error
            | .diverges => .diverged state.array
            | .done => liftMutation state.array (lastindex state.array) fun last =>
              deleteRange state.array state.destination last
theorem p3717 : P3717 := by unfold P3717; intros; rfl

/-- Vector `circshift!`, lines 3756-3766. -/
def m3756 (length : A → CResult Int) (modulo : IntegerValue → Int → CResult IntegerValue)
    (lastindex firstindex : A → CResult K)
    (subtract : K → IntegerValue → CResult K) (addOne : K → CResult K)
    (reverseRange : A → K → K → Mutation A) (reverseAll : A → Mutation A)
    (array : A) (shift : IntegerValue) : Mutation A :=
  liftMutation array (length array) fun count =>
  if count = 0 then .success array
  else liftMutation array (modulo shift count) fun normalized =>
    if normalized.value = 0 then .success array
    else liftMutation array (lastindex array) fun last =>
      liftMutation array (firstindex array) fun first =>
      liftMutation array (subtract last normalized) fun split =>
      continueMutation (reverseRange array first split) fun firstReversed =>
      liftMutation firstReversed (addOne split) fun secondStart =>
      liftMutation firstReversed (lastindex firstReversed) fun final =>
      continueMutation (reverseRange firstReversed secondStart final) fun secondReversed =>
      reverseAll secondReversed
def P3756 : Prop := ∀ {A K : Type} (length : A → CResult Int)
    (modulo : IntegerValue → Int → CResult IntegerValue)
    (lastindex firstindex : A → CResult K) (subtract : K → IntegerValue → CResult K)
    (addOne : K → CResult K) (reverseRange : A → K → K → Mutation A)
    (reverseAll : A → Mutation A) array shift,
  m3756 length modulo lastindex firstindex subtract addOne reverseRange reverseAll array shift =
    liftMutation array (length array) fun count =>
    if count = 0 then .success array
    else liftMutation array (modulo shift count) fun normalized =>
      if normalized.value = 0 then .success array
      else liftMutation array (lastindex array) fun last =>
        liftMutation array (firstindex array) fun first =>
        liftMutation array (subtract last normalized) fun split =>
        continueMutation (reverseRange array first split) fun firstReversed =>
        liftMutation firstReversed (addOne split) fun secondStart =>
        liftMutation firstReversed (lastindex firstReversed) fun final =>
        continueMutation (reverseRange firstReversed secondStart final) fun secondReversed =>
        reverseAll secondReversed
theorem p3756 : P3756 := by unfold P3756; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-map-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayMapFaithful
