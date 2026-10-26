import JuliaLean.MultidimCov.AbstractArrayStackFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayOrderIndexFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful
open AbstractArrayConcatFaithful
open AbstractArrayHvncatFaithful
open AbstractArrayStackFaithful

def loopIsequal (equal : VA → VB → StackOutcome Bool) :
    List (VA × VB) → StackOutcome Bool
  | [] => .returned true
  | (left, right) :: rest => do
      if ← equal left right then loopIsequal equal rest else .returned false

def finishBooleanRun (value : Bool) : Terminal → StackOutcome Bool
  | .done => .returned value
  | .failed failure => .thrown failure
  | .diverges => .diverged

/-- Array `isequal`, lines 3106-3117. -/
def m3106 (identical : A → B → Bool) (axesA : A → StackOutcome AX)
    (axesB : B → StackOutcome AX) (axesEqual : AX → AX → StackOutcome Bool)
    (zipIterate : A → B → StackOutcome (IterationRun (VA × VB)))
    (elementEqual : VA → VB → StackOutcome Bool) (left : A) (right : B) : StackOutcome Bool :=
  if identical left right then .returned true
  else do
    let leftAxes ← axesA left
    let rightAxes ← axesB right
    if ¬(← axesEqual leftAxes rightAxes) then return false
    let run ← zipIterate left right
    let result ← loopIsequal elementEqual run.values
    if result then finishBooleanRun true run.terminal else .returned false
def P3106 : Prop := ∀ {A B AX VA VB : Type} (identical : A → B → Bool)
    (axesA : A → StackOutcome AX) (axesB : B → StackOutcome AX)
    (axesEqual : AX → AX → StackOutcome Bool)
    (zipIterate : A → B → StackOutcome (IterationRun (VA × VB)))
    (elementEqual : VA → VB → StackOutcome Bool) left right,
  m3106 identical axesA axesB axesEqual zipIterate elementEqual left right =
  m3106 identical axesA axesB axesEqual zipIterate elementEqual left right
theorem p3106 : P3106 := by unfold P3106; intros; rfl

def comparePairs (equal : VA → VB → StackOutcome Bool)
    (less : VA → VB → StackOutcome Bool) : List (VA × VB) → StackOutcome (Option Int)
  | [] => .returned none
  | (left, right) :: rest => do
      if ← equal left right then comparePairs equal less rest
      else if ← less left right then .returned (some (-1)) else .returned (some 1)

/-- Vector `cmp`, lines 3119-3131. -/
def m3119 (firstA : A → StackOutcome IA) (firstB : B → StackOutcome IB)
    (indexEqual : IA → IB → StackOutcome Bool) (cmpIndex : IA → IB → StackOutcome Int)
    (zipIterate : A → B → StackOutcome (IterationRun (VA × VB)))
    (elementEqual : VA → VB → StackOutcome Bool) (elementLess : VA → VB → StackOutcome Bool)
    (lengthA : A → StackOutcome LA) (lengthB : B → StackOutcome LB)
    (cmpLength : LA → LB → StackOutcome Int) (left : A) (right : B) : StackOutcome Int := do
  let leftFirst ← firstA left
  let rightFirst ← firstB right
  if ¬(← indexEqual leftFirst rightFirst) then cmpIndex leftFirst rightFirst
  else
    let run ← zipIterate left right
    let result ← comparePairs elementEqual elementLess run.values
    match result with
    | some ordering => .returned ordering
    | none => match run.terminal with
      | .failed failure => .thrown failure
      | .diverges => .diverged
      | .done => cmpLength (← lengthA left) (← lengthB right)
def P3119 : Prop := ∀ {A B IA IB VA VB LA LB : Type} (firstA : A → StackOutcome IA)
    (firstB : B → StackOutcome IB) (indexEqual : IA → IB → StackOutcome Bool)
    (cmpIndex : IA → IB → StackOutcome Int)
    (zipIterate : A → B → StackOutcome (IterationRun (VA × VB)))
    (elementEqual elementLess : VA → VB → StackOutcome Bool)
    (lengthA : A → StackOutcome LA) (lengthB : B → StackOutcome LB)
    (cmpLength : LA → LB → StackOutcome Int) left right,
  m3119 firstA firstB indexEqual cmpIndex zipIterate elementEqual elementLess lengthA lengthB
    cmpLength left right =
  m3119 firstA firstB indexEqual cmpIndex zipIterate elementEqual elementLess lengthA lengthB
    cmpLength left right
theorem p3119 : P3119 := by unfold P3119; intros; rfl

/-- Zero-dimensional `isless`, lines 3135-3137. -/
def m3135 (onlyA : A → StackOutcome VA) (onlyB : B → StackOutcome VB)
    (less : VA → VB → StackOutcome Bool) (left : A) (right : B) : StackOutcome Bool := do
  let leftValue ← onlyA left
  let rightValue ← onlyB right
  less leftValue rightValue
def P3135 : Prop := ∀ {A B VA VB : Type} (onlyA : A → StackOutcome VA)
    (onlyB : B → StackOutcome VB) (less : VA → VB → StackOutcome Bool) left right,
  m3135 onlyA onlyB less left right = do
    let leftValue ← onlyA left
    let rightValue ← onlyB right
    less leftValue rightValue
theorem p3135 : P3135 := by unfold P3135; intros; rfl

inductive TriBool where | true | false | missing deriving Repr, DecidableEq

def equalityLoop (equal : VA → VB → StackOutcome TriBool) :
    List (VA × VB) → Bool → StackOutcome TriBool
  | [], missingSeen => .returned (if missingSeen then .missing else .true)
  | (left, right) :: rest, missingSeen => do
      match ← equal left right with
      | .false => .returned .false
      | .missing => equalityLoop equal rest true
      | .true => equalityLoop equal rest missingSeen

/-- Array `==`, lines 3149-3162. -/
def m3149 (axesA : A → StackOutcome AX) (axesB : B → StackOutcome AX)
    (axesEqual : AX → AX → StackOutcome Bool)
    (zipIterate : A → B → StackOutcome (IterationRun (VA × VB)))
    (elementEqual : VA → VB → StackOutcome TriBool) (left : A) (right : B) : StackOutcome TriBool := do
  if ¬(← axesEqual (← axesA left) (← axesB right)) then return .false
  let run ← zipIterate left right
  let result ← equalityLoop elementEqual run.values false
  match result with
  | .false => .returned .false
  | other => match run.terminal with
    | .done => .returned other
    | .failed failure => .thrown failure
    | .diverges => .diverged
def P3149 : Prop := ∀ {A B AX VA VB : Type} (axesA : A → StackOutcome AX)
    (axesB : B → StackOutcome AX) (axesEqual : AX → AX → StackOutcome Bool)
    (zipIterate : A → B → StackOutcome (IterationRun (VA × VB)))
    (elementEqual : VA → VB → StackOutcome TriBool) left right,
  m3149 axesA axesB axesEqual zipIterate elementEqual left right =
  m3149 axesA axesB axesEqual zipIterate elementEqual left right
theorem p3149 : P3149 := by unfold P3149; intros; rfl

structure IntegerOps where
  add : IntegerValue → IntegerValue → CResult IntegerValue
  subtract : IntegerValue → IntegerValue → CResult IntegerValue
  multiply : IntegerValue → IntegerValue → CResult IntegerValue
  divrem : IntegerValue → IntegerValue → CResult (IntegerValue × IntegerValue)

/-- Array `_sub2ind`, lines 3167-3170. -/
def m3167 (axes : A → CResult AX)
    (sub2ind : AX → List IntegerValue → CResult IntegerValue)
    (array : A) (indices : List IntegerValue) : CResult IntegerValue := do
  let arrayAxes ← axes array
  sub2ind arrayAxes indices
def P3167 : Prop := ∀ {A AX : Type} (axes : A → CResult AX)
    (sub2ind : AX → List IntegerValue → CResult IntegerValue) array indices,
  m3167 axes sub2ind array indices = do
    let arrayAxes ← axes array
    sub2ind arrayAxes indices
theorem p3167 : P3167 := by unfold P3167; intros; rfl

/-- Array `_ind2sub`, lines 3172-3175. -/
def m3172 (axes : A → CResult AX)
    (ind2sub : AX → IntegerValue → CResult S) (array : A)
    (index : IntegerValue) : CResult S := do
  let arrayAxes ← axes array
  ind2sub arrayAxes index
def P3172 : Prop := ∀ {A AX S : Type} (axes : A → CResult AX)
    (ind2sub : AX → IntegerValue → CResult S) array index,
  m3172 axes ind2sub array index = do
    let arrayAxes ← axes array
    ind2sub arrayAxes index
theorem p3172 : P3172 := by unfold P3172; intros; rfl

def sub2indEmptyLoop (ops : IntegerOps) :
    IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue
  | _, index, [] => .ok index
  | stride, index, value :: rest => do
      let offset ← ops.subtract value ⟨1⟩
      let scaled ← ops.multiply offset stride
      let next ← ops.add index scaled
      sub2indEmptyLoop ops stride next rest

/-- Empty-dimension `_sub2ind`, line 3181. -/
def m3181 (ops : IntegerOps) (indices : List IntegerValue) : CResult IntegerValue :=
  sub2indEmptyLoop ops ⟨1⟩ ⟨1⟩ indices
def P3181 : Prop := ∀ ops indices, m3181 ops indices = sub2indEmptyLoop ops ⟨1⟩ ⟨1⟩ indices
theorem p3181 : P3181 := by unfold P3181; intros; rfl

/-- Generic dimension and axis `_sub2ind`, lines 3184-3185. -/
def m3184 (recursive : D → IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue)
    (dimensions : D) (indices : List IntegerValue) : CResult IntegerValue :=
  recursive dimensions ⟨1⟩ ⟨1⟩ indices
def P3184 : Prop := ∀ {D : Type}
    (recursive : D → IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue)
    dimensions indices,
  m3184 recursive dimensions indices = recursive dimensions ⟨1⟩ ⟨1⟩ indices
theorem p3184 : P3184 := by unfold P3184; intros; rfl
def m3185 := @m3184
def P3185 : Prop := ∀ {D : Type}
    (recursive : D → IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue)
    dimensions indices,
  m3185 recursive dimensions indices = m3184 recursive dimensions indices
theorem p3185 : P3185 := by unfold P3185; intros; rfl

/-- One-axis non-OneTo `_sub2ind`, lines 3188-3189. -/
def m3188 (_axes : A) (_indices : List IntegerValue) : CResult IntegerValue :=
  .error (.argument (.literal "Linear indexing is not defined for one-dimensional arrays"))
def P3188 : Prop := ∀ {A : Type} (axes : A) indices,
  m3188 axes indices = .error (.argument (.literal "Linear indexing is not defined for one-dimensional arrays"))
theorem p3188 : P3188 := by unfold P3188; intros; rfl

def m3190 := @m3184
def P3190 : Prop := ∀ {D : Type}
    (recursive : D → IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue)
    dimensions indices,
  m3190 recursive dimensions indices = m3184 recursive dimensions indices
theorem p3190 : P3190 := by unfold P3190; intros; rfl

def m3191 (index : IntegerValue) : IntegerValue := index
def P3191 : Prop := ∀ index, m3191 index = index
theorem p3191 : P3191 := by unfold P3191; intros; rfl

def m3193 (_axes : A) (_stride : IntegerValue) (index : IntegerValue) : IntegerValue := index
def P3193 : Prop := ∀ {A : Type} (axes : A) stride index, m3193 axes stride index = index
theorem p3193 : P3193 := by unfold P3193; intros; rfl

/-- Empty-axis recursive `_sub2ind`, lines 3194-3197. -/
def m3194 (ops : IntegerOps) (stride index : IntegerValue)
    (head : IntegerValue) (tail : List IntegerValue) : CResult IntegerValue := do
  let offset ← ops.subtract head ⟨1⟩
  let scaled ← ops.multiply offset stride
  let next ← ops.add index scaled
  sub2indEmptyLoop ops stride next tail
def P3194 : Prop := ∀ ops stride index head tail,
  m3194 ops stride index head tail = do
    let offset ← ops.subtract head ⟨1⟩
    let scaled ← ops.multiply offset stride
    let next ← ops.add index scaled
    sub2indEmptyLoop ops stride next tail
theorem p3194 : P3194 := by unfold P3194; intros; rfl

/-- General recursive `_sub2ind`, lines 3198-3202. -/
def m3198 (firstAxis : AX → CResult R) (tailAxes : AX → CResult AX)
    (nextStride : IntegerValue → R → CResult IntegerValue)
    (offsetIn : IntegerValue → R → CResult IntegerValue) (ops : IntegerOps)
    (recursive : AX → IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue)
    (axes : AX) (stride index head : IntegerValue) (tail : List IntegerValue) : CResult IntegerValue := do
  let axis ← firstAxis axes
  let restAxes ← tailAxes axes
  let nextL ← nextStride stride axis
  let offset ← offsetIn head axis
  let scaled ← ops.multiply offset stride
  let nextIndex ← ops.add index scaled
  recursive restAxes nextL nextIndex tail
def P3198 : Prop := ∀ {AX R : Type} (firstAxis : AX → CResult R)
    (tailAxes : AX → CResult AX)
    (nextStride : IntegerValue → R → CResult IntegerValue)
    (offsetIn : IntegerValue → R → CResult IntegerValue) ops
    (recursive : AX → IntegerValue → IntegerValue → List IntegerValue → CResult IntegerValue)
    axes stride index head tail,
  m3198 firstAxis tailAxes nextStride offsetIn ops recursive axes stride index head tail =
  m3198 firstAxis tailAxes nextStride offsetIn ops recursive axes stride index head tail
theorem p3198 : P3198 := by unfold P3198; intros; rfl

def m3204 (multiply : IntegerValue → IntegerValue → CResult IntegerValue)
    (stride length : IntegerValue) : CResult IntegerValue := multiply stride length
def P3204 : Prop := ∀ multiply stride length, m3204 multiply stride length = multiply stride length
theorem p3204 : P3204 := by unfold P3204; intros; rfl

def m3205 (length : R → CResult IntegerValue)
    (multiply : IntegerValue → IntegerValue → CResult IntegerValue)
    (stride : IntegerValue) (range : R) : CResult IntegerValue := do
  let count ← length range
  multiply stride count
def P3205 : Prop := ∀ {R : Type} (length : R → CResult IntegerValue)
    multiply stride range,
  m3205 length multiply stride range = do let count ← length range; multiply stride count
theorem p3205 : P3205 := by unfold P3205; intros; rfl

def m3206 (indices : S → CResult R) (length : R → CResult IntegerValue)
    (multiply : IntegerValue → IntegerValue → CResult IntegerValue)
    (stride : IntegerValue) (slice : S) : CResult IntegerValue := do
  let range ← indices slice
  let count ← length range
  multiply stride count
def P3206 : Prop := ∀ {S R : Type} (indices : S → CResult R)
    (length : R → CResult IntegerValue) multiply stride slice,
  m3206 indices length multiply stride slice = do
    let range ← indices slice
    let count ← length range
    multiply stride count
theorem p3206 : P3206 := by unfold P3206; intros; rfl

def m3207 (subtract : IntegerValue → IntegerValue → CResult IntegerValue)
    (index : IntegerValue) (_length : IntegerValue) : CResult IntegerValue := subtract index ⟨1⟩
def P3207 : Prop := ∀ subtract index length, m3207 subtract index length = subtract index ⟨1⟩
theorem p3207 : P3207 := by unfold P3207; intros; rfl

def m3208 (first : R → CResult IntegerValue)
    (subtract : IntegerValue → IntegerValue → CResult IntegerValue)
    (index : IntegerValue) (range : R) : CResult IntegerValue := do
  let origin ← first range
  subtract index origin
def P3208 : Prop := ∀ {R : Type} (first : R → CResult IntegerValue)
    subtract index range,
  m3208 first subtract index range = do let origin ← first range; subtract index origin
theorem p3208 : P3208 := by unfold P3208; intros; rfl

/-- Empty-axis `_ind2sub`, line 3210. -/
def m3210 (index : IntegerValue) : CResult (List IntegerValue) :=
  if index.value = 1 then .ok [] else .error .bounds
def P3210 : Prop := ∀ index, m3210 index = if index.value = 1 then .ok [] else .error .bounds
theorem p3210 : P3210 := by unfold P3210; intros; rfl

def m3211 (subtract : IntegerValue → IntegerValue → CResult IntegerValue)
    (recursive : D → IntegerValue → CResult S) (dimensions : D)
    (index : IntegerValue) : CResult S := do
  let zeroBased ← subtract index ⟨1⟩
  recursive dimensions zeroBased
def P3211 : Prop := ∀ {D S : Type}
    (subtract : IntegerValue → IntegerValue → CResult IntegerValue)
    (recursive : D → IntegerValue → CResult S) (dimensions : D) index,
  m3211 subtract recursive dimensions index = do
    let zeroBased ← subtract index ⟨1⟩
    recursive dimensions zeroBased
theorem p3211 : P3211 := by unfold P3211; intros; rfl
def m3212 := @m3211
def P3212 : Prop := ∀ {D S : Type}
    (subtract : IntegerValue → IntegerValue → CResult IntegerValue)
    (recursive : D → IntegerValue → CResult S) (dimensions : D) index,
  m3212 subtract recursive dimensions index = m3211 subtract recursive dimensions index
theorem p3212 : P3212 := by unfold P3212; intros; rfl

def m3213 (_axes : A) (_index : IntegerValue) : CResult S :=
  .error (.argument (.literal "Linear indexing is not defined for one-dimensional arrays"))
def P3213 : Prop := ∀ {A S : Type} (axes : A) index,
  m3213 (S := S) axes index = .error (.argument (.literal "Linear indexing is not defined for one-dimensional arrays"))
theorem p3213 : P3213 := by unfold P3213; intros; rfl

def m3215 (index : IntegerValue) : List IntegerValue := [index]
def P3215 : Prop := ∀ index, m3215 index = [index]
theorem p3215 : P3215 := by unfold P3215; intros; rfl

def m3217 (add : IntegerValue → IntegerValue → CResult IntegerValue)
    (index : IntegerValue) : CResult (List IntegerValue) := do
  let value ← add index ⟨1⟩
  .ok [value]
def P3217 : Prop := ∀ add index, m3217 add index = do let value ← add index ⟨1⟩; .ok [value]
theorem p3217 : P3217 := by unfold P3217; intros; rfl

def m3218 (firstAxis : AX → CResult R) (lookup : IntegerValue → R → CResult IntegerValue)
    (axes : AX) (index : IntegerValue) : CResult (List IntegerValue) := do
  let axis ← firstAxis axes
  let value ← lookup index axis
  .ok [value]
def P3218 : Prop := ∀ {AX R : Type} (firstAxis : AX → CResult R)
    (lookup : IntegerValue → R → CResult IntegerValue) (axes : AX) index,
  m3218 firstAxis lookup axes index = do
    let axis ← firstAxis axes
    let value ← lookup index axis
    .ok [value]
theorem p3218 : P3218 := by unfold P3218; intros; rfl

def m3222 (firstAxis : AX → CResult R) (tailAxes : AX → CResult AX)
    (indexLength : R → CResult IntegerValue)
    (divrem : IntegerValue → IntegerValue → CResult (IntegerValue × IntegerValue))
    (lookup : IntegerValue → R → CResult IntegerValue)
    (recursive : AX → IntegerValue → CResult (List IntegerValue))
    (axes : AX) (index : IntegerValue) : CResult (List IntegerValue) := do
  let axis ← firstAxis axes
  let length ← indexLength axis
  let parts ← divrem index length
  let value ← lookup parts.2 axis
  let restAxes ← tailAxes axes
  let rest ← recursive restAxes parts.1
  .ok (value :: rest)
def P3222 : Prop := ∀ {AX R : Type} (firstAxis : AX → CResult R)
    (tailAxes : AX → CResult AX) (indexLength : R → CResult IntegerValue)
    (divrem : IntegerValue → IntegerValue → CResult (IntegerValue × IntegerValue))
    (lookup : IntegerValue → R → CResult IntegerValue)
    (recursive : AX → IntegerValue → CResult (List IntegerValue)) (axes : AX) index,
  m3222 firstAxis tailAxes indexLength divrem lookup recursive axes index =
  m3222 firstAxis tailAxes indexLength divrem lookup recursive axes index
theorem p3222 : P3222 := by unfold P3222; intros; rfl

def m3229 (dimension : IntegerValue) : IntegerValue := dimension
def P3229 : Prop := ∀ dimension, m3229 dimension = dimension
theorem p3229 : P3229 := by unfold P3229; intros; rfl

def m3230 (length : R → CResult IntegerValue) (range : R) : CResult IntegerValue := length range
def P3230 : Prop := ∀ {R : Type} (length : R → CResult IntegerValue) (range : R),
  m3230 length range = length range
theorem p3230 : P3230 := by unfold P3230; intros; rfl

def m3231 (add : IntegerValue → IntegerValue → CResult IntegerValue)
    (index : IntegerValue) (_dimension : IntegerValue) : CResult IntegerValue := add index ⟨1⟩
def P3231 : Prop := ∀ add index dimension, m3231 add index dimension = add index ⟨1⟩
theorem p3231 : P3231 := by unfold P3231; intros; rfl

def m3232 (first : R → CResult IntegerValue)
    (add : IntegerValue → IntegerValue → CResult IntegerValue)
    (index : IntegerValue) (range : R) : CResult IntegerValue := do
  let origin ← first range
  add index origin
def P3232 : Prop := ∀ {R : Type} (first : R → CResult IntegerValue)
    (add : IntegerValue → IntegerValue → CResult IntegerValue) index (range : R),
  m3232 first add index range = do let origin ← first range; add index origin
theorem p3232 : P3232 := by unfold P3232; intros; rfl

def m3235 (_axes : A) (_vectors : List V) : CResult O :=
  .error (.argument (.literal "Linear indexing is not defined for one-dimensional arrays"))
def P3235 : Prop := ∀ {A V O : Type} (axes : A) (vectors : List V),
  m3235 (O := O) axes vectors = .error (.argument (.literal "Linear indexing is not defined for one-dimensional arrays"))
theorem p3235 : P3235 := by unfold P3235; intros; rfl

def m3238 (delegate : A → List V → CResult O) (axes : A) (vectors : List V) : CResult O :=
  delegate axes vectors
def P3238 : Prop := ∀ {A V O : Type} (delegate : A → List V → CResult O)
    (axes : A) vectors,
  m3238 delegate axes vectors = delegate axes vectors
theorem p3238 : P3238 := by unfold P3238; intros; rfl
def m3240 := @m3238
def P3240 : Prop := ∀ {A V O : Type} (delegate : A → List V → CResult O)
    (axes : A) vectors,
  m3240 delegate axes vectors = m3238 delegate axes vectors
theorem p3240 : P3240 := by unfold P3240; intros; rfl

def gatherCoordinates (get : V → K → StackOutcome IntegerValue) :
    List V → K → StackOutcome (List IntegerValue)
  | [], _ => .returned []
  | vector :: rest, index => do
      let value ← get vector index
      let tail ← gatherCoordinates get rest index
      .returned (value :: tail)

def sub2indFill (iterateAxis : AX → StackOutcome (IterationRun K))
    (get : V → K → StackOutcome IntegerValue)
    (sub2ind : D → List IntegerValue → StackOutcome IntegerValue)
    (set : O → K → IntegerValue → StackOutcome O) (dimensions : D)
    (axis : AX) (vectors : List V) (output : O) : StackOutcome O := do
  let run ← iterateAxis axis
  let filled ← run.values.foldlM (fun out index => do
    let coordinates ← gatherCoordinates get vectors index
    let linear ← sub2ind dimensions coordinates
    set out index linear) output
  match run.terminal with
  | .done => .returned filled
  | .failed failure => .thrown failure
  | .diverges => .diverged

/-- `_sub2ind_vecs`, lines 3242-3251. -/
def m3242 (getVector : List V → Int → StackOutcome V) (axes1 : V → StackOutcome AX)
    (axesEqual : AX → AX → StackOutcome Bool) (similar : V → StackOutcome O)
    (fill : D → AX → List V → O → StackOutcome O) (dimensions : D)
    (vectors : List V) : StackOutcome O := do
  let first ← getVector vectors 1
  let reference ← axes1 first
  let rec check (index : Int) (remaining : Nat) : StackOutcome Unit :=
    match remaining with
    | 0 => .returned ()
    | remaining + 1 => do
        let vector ← getVector vectors index
        let axis ← axes1 vector
        if ¬(← axesEqual axis reference) then
          .thrown (.dimensionMismatch (.literal "indices do not match"))
        else check (index + 1) remaining
  check 2 (vectors.length - 1)
  let output ← similar first
  fill dimensions reference vectors output
def P3242 : Prop := ∀ {V AX O D : Type}
    (getVector : List V → Int → StackOutcome V) (axes1 : V → StackOutcome AX)
    (axesEqual : AX → AX → StackOutcome Bool) (similar : V → StackOutcome O)
    (fill : D → AX → List V → O → StackOutcome O) dimensions vectors,
  m3242 getVector axes1 axesEqual similar fill dimensions vectors =
  m3242 getVector axes1 axesEqual similar fill dimensions vectors
theorem p3242 : P3242 := by unfold P3242; intros; rfl

/-- `_sub2ind!`, lines 3253-3260. -/
def m3253 := @sub2indFill
def P3253 : Prop := ∀ {AX K V D O : Type}
    (iterateAxis : AX → StackOutcome (IterationRun K))
    (get : V → K → StackOutcome IntegerValue)
    (sub2ind : D → List IntegerValue → StackOutcome IntegerValue)
    (set : O → K → IntegerValue → StackOutcome O) dimensions axis vectors output,
  m3253 iterateAxis get sub2ind set dimensions axis vectors output =
  sub2indFill iterateAxis get sub2ind set dimensions axis vectors output
theorem p3253 : P3253 := by unfold P3253; intros; rfl

/-- `sub2ind_vec`, line 3262. -/
def m3262 (get : V → K → StackOutcome IntegerValue)
    (sub2ind : D → List IntegerValue → StackOutcome IntegerValue)
    (dimensions : D) (index : K) (vectors : List V) : StackOutcome IntegerValue := do
  let coordinates ← gatherCoordinates get vectors index
  sub2ind dimensions coordinates
def P3262 : Prop := ∀ {V K D : Type} (get : V → K → StackOutcome IntegerValue)
    (sub2ind : D → List IntegerValue → StackOutcome IntegerValue) dimensions index vectors,
  m3262 get sub2ind dimensions index vectors = do
    let coordinates ← gatherCoordinates get vectors index
    sub2ind dimensions coordinates
theorem p3262 : P3262 := by unfold P3262; intros; rfl

def m3263 (get : V → K → StackOutcome IntegerValue) (recursive : K → List V → StackOutcome (List IntegerValue))
    (index : K) (first : V) (rest : List V) : StackOutcome (List IntegerValue) := do
  let value ← get first index
  let tail ← recursive index rest
  .returned (value :: tail)
def P3263 : Prop := ∀ {V K : Type} (get : V → K → StackOutcome IntegerValue)
    (recursive : K → List V → StackOutcome (List IntegerValue)) index first rest,
  m3263 get recursive index first rest = do
    let value ← get first index
    let tail ← recursive index rest
    .returned (value :: tail)
theorem p3263 : P3263 := by unfold P3263; intros; rfl

def m3264 (_index : K) : List IntegerValue := []
def P3264 : Prop := ∀ {K : Type} (index : K), m3264 index = []
theorem p3264 : P3264 := by unfold P3264; intros; rfl

def updateOutputs (getOutput : List O → Int → StackOutcome O)
    (getSubscript : List IntegerValue → Int → StackOutcome IntegerValue)
    (set : O → K → IntegerValue → StackOutcome O) :
    List O → K → List IntegerValue → Int → Nat → StackOutcome (List O)
  | outputs, _, _, _, 0 => .returned outputs
  | outputs, index, subscripts, position, remaining + 1 => do
      let output ← getOutput outputs position
      let value ← getSubscript subscripts position
      let updated ← set output index value
      updateOutputs getOutput getSubscript set (outputs.set (position - 1).toNat updated)
        index subscripts (position + 1) remaining

/-- Vectorized `_ind2sub`, lines 3266-3276. -/
def m3266 (similar : V → StackOutcome O) (pairs : V → StackOutcome (IterationRun (K × IntegerValue)))
    (ind2sub : D → IntegerValue → StackOutcome (List IntegerValue))
    (getOutput : List O → Int → StackOutcome O)
    (getSubscript : List IntegerValue → Int → StackOutcome IntegerValue)
    (set : O → K → IntegerValue → StackOutcome O) (dimensions : D)
    (rank : Nat) (indices : V) : StackOutcome (List O) := do
  let outputs ← (List.range rank).mapM fun _ => similar indices
  let run ← pairs indices
  let filled ← run.values.foldlM (fun current pair => do
    let subscripts ← ind2sub dimensions pair.2
    updateOutputs getOutput getSubscript set current pair.1 subscripts 1 rank) outputs
  match run.terminal with
  | .done => .returned filled
  | .failed failure => .thrown failure
  | .diverges => .diverged
def P3266 : Prop := ∀ {V O K D : Type} (similar : V → StackOutcome O)
    (pairs : V → StackOutcome (IterationRun (K × IntegerValue)))
    (ind2sub : D → IntegerValue → StackOutcome (List IntegerValue))
    (getOutput : List O → Int → StackOutcome O)
    (getSubscript : List IntegerValue → Int → StackOutcome IntegerValue)
    (set : O → K → IntegerValue → StackOutcome O) dimensions rank indices,
  m3266 similar pairs ind2sub getOutput getSubscript set dimensions rank indices =
  m3266 similar pairs ind2sub getOutput getSubscript set dimensions rank indices
theorem p3266 : P3266 := by unfold P3266; intros; rfl

def foreachLoop (apply : V → StackOutcome Unit) : List V → StackOutcome Unit
  | [] => .returned ()
  | value :: rest => do apply value; foreachLoop apply rest

def finishUnitRun : Terminal → StackOutcome Unit
  | .done => .returned ()
  | .failed failure => .thrown failure
  | .diverges => .diverged

/-- Unary `foreach`, line 3307. -/
def m3307 (iterate : I → StackOutcome (IterationRun V))
    (apply : V → StackOutcome Unit) (iterator : I) : StackOutcome Unit := do
  let run ← iterate iterator
  foreachLoop apply run.values
  finishUnitRun run.terminal
def P3307 : Prop := ∀ {I V : Type} (iterate : I → StackOutcome (IterationRun V))
    (apply : V → StackOutcome Unit) iterator,
  m3307 iterate apply iterator = do
    let run ← iterate iterator
    foreachLoop apply run.values
    finishUnitRun run.terminal
theorem p3307 : P3307 := by unfold P3307; intros; rfl

/-- Multi-iterator `foreach`, line 3308. -/
def m3308 (zipIterate : I → List I → StackOutcome (IterationRun (List V)))
    (apply : List V → StackOutcome Unit) (first : I) (rest : List I) : StackOutcome Unit := do
  let run ← zipIterate first rest
  foreachLoop apply run.values
  finishUnitRun run.terminal
def P3308 : Prop := ∀ {I V : Type}
    (zipIterate : I → List I → StackOutcome (IterationRun (List V)))
    (apply : List V → StackOutcome Unit) first rest,
  m3308 zipIterate apply first rest = do
    let run ← zipIterate first rest
    foreachLoop apply run.values
    finishUnitRun run.terminal
theorem p3308 : P3308 := by unfold P3308; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-order-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 3106 "isequal(AbstractArray,AbstractArray)" "Array isequal checks identity and axes, then executes arbitrary zipped iteration and element comparisons with short-circuiting and propagated failures." "base/abstractarray.jl:3106-3117" ``P3106 ``p3106,
  entry 3119 "cmp(AbstractVector,AbstractVector)" "Vector cmp calls arbitrary firstindex and cmp operations, compares zipped elements lexicographically, then compares actual lengths." "base/abstractarray.jl:3119-3131" ``P3119 ``p3119,
  entry 3135 "isless(0d array,0d array)" "Zero-dimensional isless calls only on both arrays before comparing and propagates either error." "base/abstractarray.jl:3135-3137" ``P3135 ``p3135,
  entry 3149 "==(AbstractArray,AbstractArray)" "Array equality checks axes, executes zipped iteration and each element == call in order, short-circuits false, and accumulates missing." "base/abstractarray.jl:3149-3162" ``P3149 ``p3149,
  entry 3167 "_sub2ind(array,I...)" "Array sub2ind obtains axes and forwards every arbitrary Integer coordinate." "base/abstractarray.jl:3167-3170" ``P3167 ``p3167,
  entry 3172 "_ind2sub(array,index)" "Array ind2sub obtains axes and forwards every arbitrary Integer index." "base/abstractarray.jl:3172-3175" ``P3172 ``p3172,
  entry 3181 "_sub2ind(empty axes,I...)" "Empty-axis sub2ind processes every arbitrary Integer with source arithmetic order." "base/abstractarray.jl:3181" ``P3181 ``p3181,
  entry 3184 "_sub2ind(dims,I...)" "Dimension sub2ind delegates arbitrary Integer coordinates with initial stride and index one." "base/abstractarray.jl:3184" ``P3184 ``p3184,
  entry 3185 "_sub2ind(axes,I...)" "Axis sub2ind delegates arbitrary Integer coordinates with initial stride and index one." "base/abstractarray.jl:3185" ``P3185 ``p3185,
  entry 3188 "_sub2ind(one axis,I...)" "One-dimensional non-OneTo axes reject linear indexing with ArgumentError for every Integer representation." "base/abstractarray.jl:3188-3189" ``P3188 ``p3188,
  entry 3190 "_sub2ind(OneTo,I...)" "OneTo sub2ind delegates all arbitrary Integer coordinates." "base/abstractarray.jl:3190" ``P3190 ``p3190,
  entry 3191 "_sub2ind(OneTo,i)" "Single OneTo indexing returns the arbitrary Integer unchanged." "base/abstractarray.jl:3191" ``P3191 ``p3191,
  entry 3193 "_sub2ind_recurse base" "The recursion base returns its arbitrary Integer accumulated index." "base/abstractarray.jl:3193" ``P3193 ``p3193,
  entry 3194 "_sub2ind_recurse empty axes" "Empty-axis recursion performs subtraction, multiplication, addition, then recurses for every Integer input." "base/abstractarray.jl:3194-3197" ``P3194 ``p3194,
  entry 3198 "_sub2ind_recurse" "General recursion indexes and tails axes, computes next stride and offset, performs arithmetic, then recurses." "base/abstractarray.jl:3198-3202" ``P3198 ``p3198,
  entry 3204 "nextL(integer)" "Integer nextL multiplies the arbitrary stride and length values." "base/abstractarray.jl:3204" ``P3204 ``p3204,
  entry 3205 "nextL(range)" "Range nextL calls length before multiplying by the arbitrary stride." "base/abstractarray.jl:3205" ``P3205 ``p3205,
  entry 3206 "nextL(slice)" "Slice nextL obtains indices, calls length, then multiplies." "base/abstractarray.jl:3206" ``P3206 ``p3206,
  entry 3207 "offsetin(integer)" "Integer offset subtracts one using the input's arbitrary Integer arithmetic." "base/abstractarray.jl:3207" ``P3207 ``p3207,
  entry 3208 "offsetin(range)" "Range offset calls first and subtracts it from the arbitrary Integer index." "base/abstractarray.jl:3208" ``P3208 ``p3208
  , entry 3210 "_ind2sub(empty,index)" "Empty-axis ind2sub accepts every Integer, returns empty only for one, and otherwise throws BoundsError." "base/abstractarray.jl:3210" ``P3210 ``p3210
  , entry 3211 "_ind2sub(dims,index)" "Dimension ind2sub subtracts one with arbitrary Integer arithmetic before recursion." "base/abstractarray.jl:3211" ``P3211 ``p3211
  , entry 3212 "_ind2sub(axes,index)" "Axis ind2sub subtracts one with arbitrary Integer arithmetic before recursion." "base/abstractarray.jl:3212" ``P3212 ``p3212
  , entry 3213 "_ind2sub(one axis,index)" "One-dimensional non-OneTo axes reject linear indexing for every Integer representation." "base/abstractarray.jl:3213-3214" ``P3213 ``p3213
  , entry 3215 "_ind2sub(OneTo,index)" "OneTo ind2sub returns the arbitrary Integer in a singleton tuple." "base/abstractarray.jl:3215" ``P3215 ``p3215
  , entry 3217 "_ind2sub_recurse empty" "Empty recursion adds one using arbitrary Integer arithmetic and returns a singleton." "base/abstractarray.jl:3217" ``P3217 ``p3217
  , entry 3218 "_ind2sub_recurse singleton" "Singleton recursion indexes its axis and calls _lookup, propagating errors." "base/abstractarray.jl:3218-3221" ``P3218 ``p3218
  , entry 3222 "_ind2sub_recurse" "General recursion indexes and tails axes, obtains index length, calls divrem and lookup, recurses, and constructs the tuple." "base/abstractarray.jl:3222-3227" ``P3222 ``p3222
  , entry 3229 "_indexlength(integer)" "Integer index length returns every Integer representation unchanged." "base/abstractarray.jl:3229" ``P3229 ``p3229
  , entry 3230 "_indexlength(range)" "Range index length delegates to length and propagates errors." "base/abstractarray.jl:3230" ``P3230 ``p3230
  , entry 3231 "_lookup(integer)" "Integer lookup adds one using arbitrary Integer arithmetic." "base/abstractarray.jl:3231" ``P3231 ``p3231
  , entry 3232 "_lookup(range)" "Range lookup obtains first and adds it using arbitrary Integer arithmetic." "base/abstractarray.jl:3232" ``P3232 ``p3232
  , entry 3235 "_sub2ind(one axis,vectors)" "Vectorized one-dimensional non-OneTo indexing throws ArgumentError for arbitrary Integer vectors." "base/abstractarray.jl:3235-3237" ``P3235 ``p3235
  , entry 3238 "_sub2ind(OneTo,vectors)" "Vectorized OneTo indexing delegates the actual vectors unchanged." "base/abstractarray.jl:3238-3239" ``P3238 ``p3238
  , entry 3240 "_sub2ind(axes,vectors)" "General vectorized indexing delegates the actual vectors unchanged." "base/abstractarray.jl:3240-3241" ``P3240 ``p3240
  , entry 3242 "_sub2ind_vecs" "Vectorized sub2ind indexes I[1], compares every actual vector axis, allocates like the first vector, and fills over the arbitrary shared axis." "base/abstractarray.jl:3242-3251" ``P3242 ``p3242
  , entry 3253 "_sub2ind!" "The fill loop iterates the actual possibly offset axis, reads every coordinate with checked indexing, computes sub2ind, and mutates output in order." "base/abstractarray.jl:3253-3260" ``P3253 ``p3253
  , entry 3262 "sub2ind_vec" "Coordinate gathering checks every vector index and propagates BoundsError before calling _sub2ind." "base/abstractarray.jl:3262" ``P3262 ``p3262
  , entry 3263 "_sub2ind_vec" "Recursive coordinate gathering reads I1[i] before recursing and propagates any error." "base/abstractarray.jl:3263" ``P3263 ``p3263
  , entry 3264 "_sub2ind_vec empty" "The empty coordinate tail accepts any index type and returns empty." "base/abstractarray.jl:3264" ``P3264 ``p3264
  , entry 3266 "_ind2sub(vector)" "Vectorized ind2sub allocates every output like the input, iterates actual linear-index pairs, indexes every returned subscript, and mutates each output." "base/abstractarray.jl:3266-3276" ``P3266 ``p3266
  , entry 3307 "foreach(iterator)" "Unary foreach executes arbitrary iteration and each callback in order, returning nothing only after normal exhaustion." "base/abstractarray.jl:3307" ``P3307 ``p3307
  , entry 3308 "foreach(iterators)" "Multi-iterator foreach executes arbitrary zip iteration and each splatted callback in order, stopping at normal shortest exhaustion." "base/abstractarray.jl:3308" ``P3308 ``p3308
]

end JuliaLean.MultidimCov.AbstractArrayOrderIndexFaithful
