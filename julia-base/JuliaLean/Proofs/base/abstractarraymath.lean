import JuliaLean.base.abstractarraymath
import JuliaLean.base.array
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.abstractarraymath.broadcast_arrays
import JuliaLean.Proofs.base.abstractarraymath.cartesian_shapes
import JuliaLean.Proofs.base.abstractarraymath.cartesian_refutations
import JuliaLean.Proofs.base.abstractarraymath.circshift

/-!
# Properties of `base/abstractarraymath.jl`

The predicates quantify over arrays and use the method's typed interfaces. Array contents, axes,
allocation, broadcasting, and iteration remain explicit interface values. Registry entries are open
for the proof worker; this file contains specifications only.
-/

namespace JuliaLean.Proofs.base.abstractarraymath

open JuliaLean JuliaLean.base.array JuliaLean.base.abstractarraymath JuliaLean.Registry

abbrev I64 := JInt .i64
abbrev Result (α : Type) := Except Error α
abbrev MutationM (α : Type) := JuliaLean.base.abstractarraymath.MutationM α


/-- Run a stateful array method and retain both its outcome and final heap. -/
def runMutation {α β : Type} (m : MutationM α β) (state : MutableMemory α) :
    Except Error β × MutableMemory α := m.run.run state

/-! ## Basic array operations -/

def ArrayPredicateSpec : Prop :=
  ∀ (E A : Type) (all : (E → Bool) → A → Result Bool) (elements : A → List E)
    (isreal iszero : E → Bool) (a : A),
    (∀ (p : E → Bool) (x : A), all p x = .ok ((elements x).all p)) →
      (isrealArray all isreal a = .ok true ↔ ∀ x ∈ elements a, isreal x = true) ∧
      (iszeroArray all iszero a = .ok true ↔ ∀ x ∈ elements a, iszero x = true) ∧
      isrealRealArray a = true

def VectorizationSpec : Prop :=
  ∀ (A B : Type) (length : A → Result I64) (reshape : A → I64 → Result B)
    (size : B → Result I64) (sharesStorage : A → B → Prop) (a : A),
    (∀ n, length a = .ok n → ∃ b, reshape a n = .ok b) →
    (∀ n b, reshape a n = .ok b → size b = .ok n ∧ sharesStorage a b) →
    (∃ b, vecArray length reshape a = .ok b ∧ size b = length a ∧ sharesStorage a b) ∧
      vecVector a = a

def droppedAxes {Ax : Type} (axes : List Ax) (dims : List I64) : List Ax :=
  ((List.range axes.length : List Nat).filterMap fun (k : Nat) =>
    if dims.contains (JuliaLean.base.abstractarraymath.int (k + 1)) then none else axes[k]?)

def hasDuplicateI64 : List I64 → Bool
  | [] => false
  | d :: ds => ds.contains d || hasDuplicateI64 ds

def insertedAxes {Ax : Type} (axes : List Ax) (dims : List I64) (oneTo : I64 → Ax) : List Ax :=
  let (_, result) := (List.range (axes.length + dims.length)).foldl
    (fun (source : Nat × List Ax) (k : Nat) =>
      if dims.contains (JuliaLean.base.abstractarraymath.int (k + 1)) then
        (source.1, source.2 ++ [oneTo (JuliaLean.base.abstractarraymath.int 1)])
      else match axes[source.1]? with
        | none => (source.1 + 1, source.2)
        | some ax => (source.1 + 1, source.2 ++ [ax])) (0, [])
  result

def DropdimsSpec : Prop :=
  ∀ (A Ax B : Type) (eachindex : List I64 → List I64)
    (getindex : List I64 → I64 → Result I64) (ndims : A → I64)
    (axesDim : A → I64 → Result Ax) (axisLength : Ax → Result I64)
    (axes : A → Result (List Ax))
    (foldOneto : {S : Type} → (S → I64 → Result S) → S → I64 → Result S)
    (isConcreteAxesType : List Ax → Bool) (typeofAxes : List Ax → TypeToken)
    (assertAxesType : TypeToken → List Ax → Result (List Ax))
    (reshape : A → List Ax → Result B) (axesOf : B → Result (List Ax))
    (sharesStorage : A → B → Prop) (a : A) (dims : List I64),
    let model := dropdimsDims eachindex getindex ndims axesDim axisLength axes foldOneto
      isConcreteAxesType subTupleDispatch typeofAxes assertAxesType reshape
    let result := dropdims model a dims
    let dimensionsInspectable :=
      ∀ d, d ∈ dims → int 1 ≤ d → d ≤ ndims a →
        ∃ ax n, axesDim a d = .ok ax ∧ axisLength ax = .ok n
    ((∀ out, result = .ok out →
        ∃ oldAxes, axes a = .ok oldAxes ∧
          axesOf out = .ok (droppedAxes oldAxes dims) ∧ sharesStorage a out) ∧
      (dimensionsInspectable →
        ((∀ d, d ∈ dims → (d.val < 1 ∨ ndims a < d) →
            ∃ message, result = .error (.argument message)) ∧
          (hasDuplicateI64 dims = true →
            ∃ message, result = .error (.argument message)) ∧
          (∀ d ax n, d ∈ dims → axesDim a d = .ok ax → axisLength ax = .ok n →
            n ≠ int 1 → ∃ message, result = .error (.argument message)))) ∧
      (∀ (D : Type) (toInt : D → Result I64) (dim : D) (error : Error),
        toInt dim = .error error → dropdimsInteger toInt model a dim = .error error) ∧
      (∀ (D : Type) (toInt : D → Result I64) (dim : D) (d : I64) (out : B),
        toInt dim = .ok d → dropdimsInteger toInt model a dim = .ok out →
          ∃ oldAxes, axes a = .ok oldAxes ∧
            axesOf out = .ok (droppedAxes oldAxes [d]) ∧ sharesStorage a out))

def InsertdimsSpec : Prop :=
  ∀ (A Ax B : Type) (eachindex : List I64 → List I64)
    (getindex : List I64 → I64 → Result I64) (rank : Nat)
    (axesDim : A → I64 → Result Ax) (oneTo : I64 → Ax)
    (foldOneto : {S : Type} → (S → I64 → Result S) → S → I64 → Result S)
    (reshape : A → List Ax → Result B) (axes : A → Result (List Ax))
    (axesOf : B → Result (List Ax)) (sharesStorage : A → B → Prop)
    (a : A) (dims : List I64),
    let insert := insertdimsDims eachindex getindex rank axesDim oneTo foldOneto reshape
    ((∀ out, insertdims insert a dims = .ok out →
        ∃ oldAxes, axes a = .ok oldAxes ∧
          axesOf out = .ok (insertedAxes oldAxes dims oneTo) ∧ sharesStorage a out) ∧
      (∀ d, d ∈ dims →
        (d.val < 1 ∨ Int.ofNat (rank + dims.length) < d.val) →
          ∃ message, insertdims insert a dims = .error (.argument message)) ∧
      (hasDuplicateI64 dims = true →
        ∃ message, insertdims insert a dims = .error (.argument message)) ∧
      (∀ (D : Type) (toInt : D → Result I64) (dim : D) (error : Error),
        toInt dim = .error error → insertdimsInteger toInt insert a dim = .error error) ∧
      (∀ (D : Type) (toInt : D → Result I64) (dim : D) (d : I64) (out : B),
        toInt dim = .ok d → insertdimsInteger toInt insert a dim = .ok out →
          ∃ oldAxes, axes a = .ok oldAxes ∧
            axesOf out = .ok (insertedAxes oldAxes [d] oneTo) ∧ sharesStorage a out))


/-! ## Unary array transformations -/

def ArrayTransformSpec : Prop :=
  ∀ (A E F B : Type) (broadcast : (E → F) → A → Result B)
    (elements : A → List E) (outputElements : B → List F)
    (shape : A → List Nat) (outputShape : B → List Nat)
    (conj real imag neg : E → F) (a : A),
    (∀ (f : E → F) x out, broadcast f x = .ok out →
      outputElements out = (elements x).map f ∧ outputShape out = shape x) →
    (∀ out, conjArray broadcast conj a = .ok out →
      outputElements out = (elements a).map conj ∧ outputShape out = shape a) ∧
    (∀ out, realArray broadcast real a = .ok out →
      outputElements out = (elements a).map real ∧ outputShape out = shape a) ∧
    (∀ out, imagArray broadcast imag a = .ok out →
      outputElements out = (elements a).map imag ∧ outputShape out = shape a) ∧
    (∀ out, negArray broadcast neg a = .ok out →
      outputElements out = (elements a).map neg ∧ outputShape out = shape a)

def ArrayIdentitySpec : Prop :=
  ∀ (A : Type) (a : A),
    conjBangReal a = a ∧ conjRealArray a = a ∧ realRealArray a = a ∧
    unaryPlusArray a = a ∧ unaryMulArray a = a

def ImaginaryRealArraySpec : Prop :=
  ∀ (A B : Type) (zero : A → Result B) (shape : A → List Nat)
    (outputShape : B → List Nat) (allZero : B → Prop) (a : A),
    (∀ b, zero a = .ok b → outputShape b = shape a ∧ allZero b) →
    ∀ b, imagRealArray zero a = .ok b → outputShape b = shape a ∧ allZero b

def ConjBangNumbersSpec : Prop :=
  ∀ (E A : Type) (contents : MutableMemory E → A → List E)
    (broadcastBang : (E → E) → A → A → MutationM E Unit)
    (conj : E → E) (a : A) (before after : MutableMemory E) (out : A),
    (∀ f x state final,
      runMutation (broadcastBang f x x) state = (.ok (), final) →
        contents final x = (contents state x).map f) →
    runMutation (conjBangNumbers broadcastBang conj a) before = (.ok out, after) →
      out = a ∧ contents after a = (contents before a).map conj

def ConjBangNestedSpec : Prop :=
  ∀ (E A : Type) (contents : MutableMemory E → A → List E)
    (allConjugated : MutableMemory E → E → Prop)
    (foreach : (E → MutationM E Unit) → A → MutationM E Unit)
    (conjBang : E → MutationM E Unit) (a : A) (before after : MutableMemory E)
    (out : A),
    (∀ op x initial final,
      runMutation (foreach op x) initial = (.ok (), final) →
        ∀ e ∈ contents initial x, allConjugated final e) →
    runMutation (conjBangNested foreach conjBang a) before = (.ok out, after) →
      out = a ∧ ∀ e ∈ contents before a, allConjugated after e

/-! ## `selectdim` contracts -/

structure SelectdimInterfaces (A D Ix Ax V : Type) where
  axes : A → Result (List Ax)
  colon : Ix
  setindex : Ix → D → List Ix → List Ix
  dimensionAtLeastOne : D → Result Bool
  showDim : D → String
  ndims : A → I64
  dimensionGreater : D → I64 → Result Bool
  indexEqualsOne : Ix → Result Bool
  minusOne : D → Result D
  ntupleColons : D → Result (List Ix)
  boundsError : A → List Ix → Error
  view : A → List Ix → Result V
  dimensionToNat : D → Nat
  oneDimensional : Ix → Prop
  isSlice : Ix → Prop
  viewInBounds : A → V → Bool

def selectedIndices {Ix : Type} (rank dimension : Nat) (index colon : Ix) : List Ix :=
  List.replicate (dimension - 1) colon ++ [index] ++ List.replicate (rank - dimension) colon

def SelectdimInRange : Prop :=
  ∀ (A D Ix Ax V : Type) (ops : SelectdimInterfaces A D Ix Ax V) (a : A) (d : D) (i : Ix),
    (∃ axes, ops.axes a = .ok axes ∧
      ops.setindex i d (axes.map fun _ => ops.colon) =
        selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon) →
    ops.dimensionAtLeastOne d = .ok true →
    ops.dimensionGreater d (ops.ndims a) = .ok false →
    ops.oneDimensional i →
    selectdim ops.axes ops.colon ops.setindex
      (selectdimInternal ops.dimensionAtLeastOne ops.showDim ops.ndims ops.dimensionGreater
        ops.indexEqualsOne ops.minusOne ops.ntupleColons ops.boundsError ops.view)
      a d i = ops.view a (selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon)

def SelectdimViewAgrees : Prop :=
  ∀ (A D Ix Ax V : Type) (ops : SelectdimInterfaces A D Ix Ax V) (a : A) (d : D) (i : Ix),
    (∃ axes, ops.axes a = .ok axes ∧
      ops.setindex i d (axes.map fun _ => ops.colon) =
        selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon) →
    ops.dimensionAtLeastOne d = .ok true →
    ops.oneDimensional i →
    selectdim ops.axes ops.colon ops.setindex
      (selectdimInternal ops.dimensionAtLeastOne ops.showDim ops.ndims ops.dimensionGreater
        ops.indexEqualsOne ops.minusOne ops.ntupleColons ops.boundsError ops.view)
      a d i = ops.view a (selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon)

def SelectdimInBounds : Prop :=
  ∀ (A D Ix Ax V : Type) (ops : SelectdimInterfaces A D Ix Ax V) (a : A) (d : D) (i : Ix),
    (∃ axes, ops.axes a = .ok axes ∧
      ops.setindex i d (axes.map fun _ => ops.colon) =
        selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon) →
    ¬ ops.isSlice i →
    match selectdim ops.axes ops.colon ops.setindex
      (selectdimInternal ops.dimensionAtLeastOne ops.showDim ops.ndims ops.dimensionGreater
        ops.indexEqualsOne ops.minusOne ops.ntupleColons ops.boundsError ops.view)
      a d i with
    | .error _ => True
    | .ok view => ops.viewInBounds a view = true

/-! ## `circshift` data contract -/

def shiftedCoordinate (coordinate size shift : Int) : Int :=
  if size ≤ 0 then coordinate else Int.emod (coordinate - 1 - shift) size + 1

def shiftedCoordinates : List Int → List Int → List Int → List Int
  | [], _, _ => []
  | coordinate :: coordinates, size :: sizes, [] =>
      shiftedCoordinate coordinate size 0 :: shiftedCoordinates coordinates sizes []
  | coordinate :: coordinates, size :: sizes, shift :: shifts =>
      shiftedCoordinate coordinate size shift :: shiftedCoordinates coordinates sizes shifts
  | _, _, _ => []

structure ShiftObservation (E A Ix : Type) where
  shape : A → List Int
  indices : A → List Ix
  coordinates : Ix → List Int
  indexAt : A → List Int → Ix
  contents : MutableMemory E → A → Ix → Option E

def CircularShiftSpec : Prop :=
  ∀ (E A Ix R V : Type) (observation : ShiftObservation E A Ix)
    (similar : A → MutationM E A) (toInteger : R → MutationM E I64)
    (splat : V → MutationM E (List R)) (circshiftBang : A → A → List I64 → MutationM E A)
    (a : A) (state : MutableMemory E),
    (∀ x dest before after,
      runMutation (similar x) before = (.ok dest, after) →
        ∀ ix ∈ observation.indices x,
          observation.contents after x ix = observation.contents before x ix) →
    (∀ dest src shifts before out final,
      runMutation (circshiftBang dest src shifts) before = (.ok out, final) →
        ∀ ix ∈ observation.indices src,
          observation.contents final out ix =
            observation.contents before src
              (observation.indexAt src
                (shiftedCoordinates (observation.coordinates ix) (observation.shape src)
                  (shifts.map fun x => x.val)))) →
    (∀ shift before converted after,
      runMutation (toInteger shift) before = (.ok converted, after) →
        ∀ ix ∈ observation.indices a,
          observation.contents after a ix = observation.contents before a ix) →
    (∀ shift before values after,
      runMutation (splat shift) before = (.ok values, after) →
        ∀ ix ∈ observation.indices a,
          observation.contents after a ix = observation.contents before a ix) →
    (∀ (shift : R) (dest : A) (afterSimilar : MutableMemory E) (converted : I64)
      (afterConversion : MutableMemory E) (out : A) (final : MutableMemory E),
      runMutation (similar a) state = (.ok dest, afterSimilar) →
      runMutation (toInteger shift) afterSimilar = (.ok converted, afterConversion) →
      runMutation (circshiftReal similar toInteger circshiftBang a shift) state = (.ok out, final) →
      ∀ ix ∈ observation.indices a,
        observation.contents final out ix =
          observation.contents state a
            (observation.indexAt a
              (shiftedCoordinates (observation.coordinates ix) (observation.shape a) [converted.val]))) ∧
    (∀ (shifts : List I64) (out : A) (final : MutableMemory E),
      runMutation (circshiftDims similar circshiftBang a shifts) state = (.ok out, final) →
      ∀ ix ∈ observation.indices a,
        observation.contents final out ix =
          observation.contents state a
            (observation.indexAt a (shiftedCoordinates (observation.coordinates ix)
              (observation.shape a) (shifts.map fun x => x.val)))) ∧
    (∀ (shift : V) (dest : A) (afterSimilar : MutableMemory E) (values : List R)
      (afterSplat : MutableMemory E) (converted : List I64)
      (afterConversion : MutableMemory E) (out : A) (final : MutableMemory E),
      runMutation (similar a) state = (.ok dest, afterSimilar) →
      runMutation (splat shift) afterSimilar = (.ok values, afterSplat) →
      runMutation (mapMList toInteger values) afterSplat = (.ok converted, afterConversion) →
      runMutation (circshiftGeneric similar splat toInteger circshiftBang a shift) state =
        (.ok out, final) →
      ∀ ix ∈ observation.indices a,
        observation.contents final out ix =
          observation.contents state a
            (observation.indexAt a (shiftedCoordinates (observation.coordinates ix)
              (observation.shape a) (converted.map fun x => x.val))))

/-! ## Repetition contracts -/

structure RepeatContext (α A E C I Ix Selector : Type) where
  arrayOps : RepeatArrayOps α A E C Ix Selector
  rank : A → Nat
  requireOneBased : A → MutationM α Unit
  isInteger : C → Bool
  isNegative : C → Bool
  all : (C → MutationM α Bool) → CountArg C I → MutationM α Bool
  any : (C → MutationM α Bool) → CountArg C I → MutationM α Bool
  countLength : CountArg C I → MutationM α I64
  ndims : A → I64
  showCounts : CountArg C I → String
  collect : I → MutationM α (List C)
  tuple : List C → List C
  fillToLength : List C → C → Nat → List C
  reshape : A → List C → MutationM α A

def padOnes {C : Type} (one : C) (values : List C) (n : Nat) : List C :=
  values ++ List.replicate (n - values.length) one

def expectedRepeatShape {C : Type} (one : C) (mul : C → C → C)
    (size : List C) (inner outer : Option (List C)) : List C :=
  let n := max size.length (max ((inner.map List.length).getD 0) ((outer.map List.length).getD 0))
  let sizes := padOnes one size n
  let inners := padOnes one (inner.getD []) n
  let outers := padOnes one (outer.getD []) n
  (List.range n).map fun i => mul (mul (sizes.getD i one) (inners.getD i one)) (outers.getD i one)

def RepeatShape : Prop :=
  ∀ (α A E C I Ix Selector : Type) (ctx : RepeatContext α A E C I Ix Selector)
    (arr : A) (inner outer : Option (List C)) (state : MutableMemory α)
    (sourceSize : List C) (out : A) (final : MutableMemory α),
    let innerArg := inner.map CountArg.tuple
    let outerArg := outer.map CountArg.tuple
    let check := RepeatInnerOuter.checkDispatch ctx.requireOneBased ctx.isInteger ctx.isNegative
      ctx.all ctx.any ctx.countLength ctx.ndims ctx.showCounts
    let resolve := RepeatInnerOuter.resolveDispatch ctx.rank ctx.arrayOps.size ctx.collect ctx.tuple
      ctx.fillToLength ctx.arrayOps.one ctx.reshape
    let repeatFn := RepeatInnerOuter.repeatInnerOuterDispatch ctx.arrayOps ctx.rank
    (∀ a dims before reshaped after,
      runMutation (ctx.reshape a dims) before = (.ok reshaped, after) →
        runMutation (ctx.arrayOps.size reshaped) after = (.ok dims, after)) →
    runMutation (ctx.arrayOps.size arr) state = (.ok sourceSize, state) →
    runMutation (check arr innerArg outerArg) state = (.ok (), state) →
    runMutation (repeatKeyword
      (fun a inner outer => RepeatInnerOuter.repeatModule check resolve repeatFn a inner outer)
      arr innerArg outerArg) state = (.ok out, final) →
    (runMutation (ctx.arrayOps.size out) final).1 =
      .ok (expectedRepeatShape ctx.arrayOps.one ctx.arrayOps.mul sourceSize inner outer)

def repeatCountFailure {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A)
    (state : MutableMemory α) (counts : CountArg C I) (checkLength : Bool) : Prop :=
  let allResult := runMutation (ctx.all (fun x => pure (ctx.isInteger x)) counts) state
  allResult.2 = state ∧
    (allResult.1 = .ok false ∨
      (allResult.1 = .ok true ∧
        let negativeResult := runMutation (ctx.any (fun x => pure (ctx.isNegative x)) counts) state
        negativeResult.2 = state ∧
          (negativeResult.1 = .ok true ∨
            (negativeResult.1 = .ok false ∧ checkLength = true ∧
              ∃ n, runMutation (ctx.countLength counts) state = (.ok n, state) ∧
                n < ctx.ndims a))))

def repeatCountValid {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A)
    (state : MutableMemory α) (counts : CountArg C I) : Prop :=
  let allResult := runMutation (ctx.all (fun x => pure (ctx.isInteger x)) counts) state
  let negativeResult := runMutation (ctx.any (fun x => pure (ctx.isNegative x)) counts) state
  allResult = (.ok true, state) ∧ negativeResult = (.ok false, state) ∧
    ∃ n, runMutation (ctx.countLength counts) state = (.ok n, state) ∧ ctx.ndims a ≤ n

def RepeatCheckSpec : Prop :=
  ∀ (α A E C I Ix Selector : Type) (ctx : RepeatContext α A E C I Ix Selector)
    (a : A) (inner outer : Option (CountArg C I)) (state : MutableMemory α),
    (inner.isSome = true →
      runMutation (ctx.requireOneBased a) state = (.ok (), state)) →
    (let innerInvalid := match inner with
      | none => False
      | some counts => repeatCountFailure ctx a state counts true
    let outerInvalid := match outer with
      | none => False
      | some counts => repeatCountFailure ctx a state counts inner.isSome
    let innerValid := match inner with
      | none => True
      | some counts => repeatCountValid ctx a state counts
    innerInvalid ∨ (outerInvalid ∧ innerValid)) →
    match (runMutation
      (RepeatInnerOuter.check ctx.requireOneBased ctx.isInteger ctx.isNegative
        ctx.all ctx.any ctx.countLength ctx.ndims ctx.showCounts a inner outer) state).1 with
    | .error (.argument _) => True
    | _ => False
def RepeatFullSpec : Prop := RepeatShape ∧ RepeatCheckSpec

def RepeatVectorContent : Prop :=
  ∀ (E Ix Selector : Type) (ops : RepeatArrayOps E Nat E Int Ix Selector)
    (a : Nat) (inner outer n : Int) (state : MutableMemory E),
    runMutation (ops.length a) state = (.ok n, state) →
    0 < n → 0 < inner → 0 < outer →
    n * inner * outer ≤ IntTy.max .i64 →
    ∃ out final,
      runMutation
        (RepeatInnerOuter.repeatInnerOuterBoth (RepeatInnerOuter.repeatInner ops)
          (RepeatInnerOuter.repeatOuterDispatch ops (fun _ : Nat => 1)) a [inner] [outer]) state = (.ok out, final) ∧
      ∀ k : Int, 1 ≤ k → k ≤ n * inner * outer →
        (runMutation (ops.getindex out (ops.cartesianIndex [k])) final).1 =
          (runMutation
            (ops.getindex a (ops.cartesianIndex
              [Int.ediv (Int.emod (k - 1) (n * inner)) inner + 1])) state).1

def RepeatVectorOverflow : Prop :=
  ∀ (E Ix Selector : Type) (ops : RepeatArrayOps E Nat E Int Ix Selector)
    (a : Nat) (inner outer n : Int) (state : MutableMemory E),
    runMutation (ops.length a) state = (.ok n, state) →
    0 ≤ inner → 0 ≤ outer →
    (n * inner > IntTy.max .i64 ∨ n * inner * outer > IntTy.max .i64) →
    (runMutation
      (RepeatInnerOuter.repeatInnerOuterBoth (RepeatInnerOuter.repeatInner ops)
        (RepeatInnerOuter.repeatOuterDispatch ops (fun _ : Nat => 1)) a [inner] [outer]) state).1 = .error .overflow

def RepeatVectorSpec : Prop := RepeatVectorContent ∧ RepeatVectorOverflow ∧ RepeatShape

/-! ## Registry entries -/

end JuliaLean.Proofs.base.abstractarraymath


/-! Completed array contracts and reusable partial results for batch 4, group 24. -/

namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean
open JuliaLean.base.array JuliaLean.base.abstractarraymath
open JuliaLean.Proofs.base.abstractarraymath

/-- aam-array-predicates -/
theorem AamArrayPredicates : JuliaLean.Proofs.base.abstractarraymath.ArrayPredicateSpec := by
  intro E A all elements isreal iszero a hall
  constructor
  · change all isreal a = .ok true ↔ _
    rw [hall]
    simp only [Except.ok.injEq, List.all_eq_true]
  constructor
  · change all iszero a = .ok true ↔ _
    rw [hall]
    simp only [Except.ok.injEq, List.all_eq_true]
  · rfl

/-- Vectorization's documented conclusion once the input length is known to succeed. -/
theorem aam_vec_when_length_succeeds (A B : Type)
    (length : A → Except Error (JInt .i64))
    (reshape : A → JInt .i64 → Except Error B)
    (size : B → Except Error (JInt .i64)) (sharesStorage : A → B → Prop)
    (a : A) (n : JInt .i64) (hlen : length a = .ok n)
    (hreshape : ∀ n, length a = .ok n → ∃ b, reshape a n = .ok b)
    (hresult : ∀ n b, reshape a n = .ok b → size b = .ok n ∧ sharesStorage a b) :
    (∃ b, vecArray length reshape a = .ok b ∧ size b = length a ∧ sharesStorage a b) ∧
      vecVector a = a := by
  obtain ⟨b, hb⟩ := hreshape n hlen
  refine ⟨⟨b, ?_, (hresult n b hb).1.trans hlen.symm, (hresult n b hb).2⟩, rfl⟩
  simp only [vecArray, hlen, bind, Except.bind, hb]

/-- Length failures propagate; the frozen vectorization statement omits this possibility. -/
theorem aam_vec_length_error (A B : Type)
    (length : A → Except Error (JInt .i64))
    (reshape : A → JInt .i64 → Except Error B) (a : A) (error : Error)
    (h : length a = .error error) : vecArray length reshape a = .error error := by
  simp only [vecArray, h, bind, Except.bind]

/-- Conversion-error component of the dropdims contract. -/
theorem aam_dropdims_conversion_error (A D B : Type)
    (toInt : D → Except Error (JInt .i64))
    (drop : A → List (JInt .i64) → Except Error B) (a : A) (dim : D) (error : Error)
    (h : toInt dim = .error error) : dropdimsInteger toInt drop a dim = .error error := by
  simp only [dropdimsInteger, h, bind, Except.bind]

/-- A successful scalar conversion forwards one dimension to the dropdims implementation. -/
theorem aam_dropdims_conversion_success (A D B : Type)
    (toInt : D → Except Error (JInt .i64))
    (drop : A → List (JInt .i64) → Except Error B) (a : A) (dim : D) (d : JInt .i64)
    (h : toInt dim = .ok d) : dropdimsInteger toInt drop a dim = drop a [d] := by
  simp only [dropdimsInteger, h, bind, Except.bind]

/-- Conversion-error component of the insertdims contract. -/
theorem aam_insertdims_conversion_error (A D B : Type)
    (toInt : D → Except Error (JInt .i64))
    (insert : A → List (JInt .i64) → Except Error B) (a : A) (dim : D) (error : Error)
    (h : toInt dim = .error error) : insertdimsInteger toInt insert a dim = .error error := by
  simp only [insertdimsInteger, h, bind, Except.bind]

/-- A successful scalar conversion forwards one dimension to the insertdims implementation. -/
theorem aam_insertdims_conversion_success (A D B : Type)
    (toInt : D → Except Error (JInt .i64))
    (insert : A → List (JInt .i64) → Except Error B) (a : A) (dim : D) (d : JInt .i64)
    (h : toInt dim = .ok d) : insertdimsInteger toInt insert a dim = insert a [d] := by
  simp only [insertdimsInteger, h, bind, Except.bind]

/-- aam-elementwise -/
theorem AamElementwise : JuliaLean.Proofs.base.abstractarraymath.ArrayTransformSpec := by
  intro A E F B broadcast elements outputElements shape outputShape conj real imag neg a h
  exact ⟨h conj a, h real a, h imag a, h neg a⟩

/-- aam-array-identities -/
theorem AamArrayIdentities : JuliaLean.Proofs.base.abstractarraymath.ArrayIdentitySpec := by
  intro A a
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- aam-imag-real-zero -/
theorem AamImagRealZero : JuliaLean.Proofs.base.abstractarraymath.ImaginaryRealArraySpec := by
  intro A B zero shape outputShape allZero a h
  exact h

/-- A stateful effect followed by returning the input retains the effect's final state. -/
theorem aam_effect_then_return {E A : Type}
    (effect : JuliaLean.base.array.MutationM E Unit) (a out : A)
    (before after : MutableMemory E)
    (h : runMutation (do effect; pure a) before = (.ok out, after)) :
    out = a ∧ runMutation effect before = (.ok (), after) := by
  simp only [runMutation, bind, ExceptT.bind, StateT.bind, pure, ExceptT.pure,
    ExceptT.run, ExceptT.mk, ExceptT.bindCont, StateT.run] at h
  cases he : effect.run before with
  | mk result final =>
    cases result with
    | error error =>
      simp only [ExceptT.run] at he
      rw [he] at h
      cases h
    | ok value =>
      cases value
      simp only [ExceptT.run] at he
      rw [he] at h
      simp only [StateT.pure, pure, Prod.mk.injEq, Except.ok.injEq] at h
      refine ⟨h.1.symm, ?_⟩
      change effect before = (Except.ok (), after)
      rw [he, h.2]

/-- aam-conj-bang-numbers -/
theorem AamConjBangNumbers : JuliaLean.Proofs.base.abstractarraymath.ConjBangNumbersSpec := by
  intro E A contents broadcastBang conj a before after out hb h
  obtain ⟨hout, heffect⟩ := aam_effect_then_return (broadcastBang conj a a) a out before after h
  exact ⟨hout, hb conj a before after heffect⟩

/-- aam-conj-bang-nested -/
theorem AamConjBangNested : JuliaLean.Proofs.base.abstractarraymath.ConjBangNestedSpec := by
  intro E A contents allConjugated foreach conjBang a before after out hf h
  obtain ⟨hout, heffect⟩ := aam_effect_then_return (foreach conjBang a) a out before after h
  exact ⟨hout, hf conjBang a before after heffect⟩

/-- multidim-selectdim-in-range -/
theorem MultidimSelectdimInRange : JuliaLean.Proofs.base.abstractarraymath.SelectdimInRange := by
  intro A D Ix Ax V ops a d i haxes hmin hmax hi
  obtain ⟨axes, haxes, hindices⟩ := haxes
  simp only [selectdim, haxes, Except.bind, bind]
  rw [hindices]
  simp only [selectdimInternal, hmin, hmax, Except.bind, bind,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte]

inductive AamTrailingIndex where
  | colon
  | oneRange
  deriving DecidableEq

def aamTrailingView (a : List Int) (indices : List AamTrailingIndex) :
    Except Error (List Nat) :=
  match indices with
  | [] => if a.length = 1 then .ok [] else .error .bounds
  | index :: rest =>
      if index = .oneRange ∧ a.isEmpty then .error .bounds
      else .ok ((if index = .colon then a.length else 1) :: rest.map (fun _ => 1))

def aamTrailingOps : SelectdimInterfaces (List Int) Nat AamTrailingIndex Nat (List Nat) where
  axes a := .ok [a.length]
  colon := .colon
  setindex i d indices := indices.take (d - 1) ++
    List.replicate (d - 1 - indices.length) .colon ++ [i] ++ indices.drop d
  dimensionAtLeastOne d := .ok (decide (1 ≤ d))
  showDim d := toString d
  ndims _ := int 1
  dimensionGreater d n := .ok (decide (n.val < Int.ofNat d))
  indexEqualsOne _ := .ok false
  minusOne d := .ok (d - 1)
  ntupleColons d := .ok (List.replicate d .colon)
  boundsError _ _ := .bounds
  view := aamTrailingView
  dimensionToNat d := d
  oneDimensional _ := True
  isSlice i := i = .colon
  viewInBounds _ _ := true

theorem MultidimSelectdimTrailing :
    ¬ JuliaLean.Proofs.base.abstractarraymath.SelectdimViewAgrees := by
  intro h
  have bad := h (List Int) Nat AamTrailingIndex Nat (List Nat) aamTrailingOps
    [10, 20] 2 .oneRange ⟨[2], rfl, rfl⟩ rfl True.intro
  change (Except.error Error.bounds : Except Error (List Nat)) = .ok [2, 1] at bad
  cases bad

theorem aam_run_bind {E A B : Type} (m : JuliaLean.base.array.MutationM E A)
    (f : A → JuliaLean.base.array.MutationM E B) (state : MutableMemory E) :
    runMutation (m >>= f) state =
      match runMutation m state with
      | (.error error, after) => (.error error, after)
      | (.ok value, after) => runMutation (f value) after := by
  simp only [runMutation, bind, ExceptT.bind, ExceptT.run, ExceptT.mk, StateT.bind, StateT.run]
  cases h : m state with
  | mk result after =>
    cases result <;> rfl

theorem aam_run_pure {E A : Type} (value : A) (state : MutableMemory E) :
    runMutation (pure value) state = (Except.ok value, state) := rfl

theorem aam_run_throw {E A : Type} (error : Error) (state : MutableMemory E) :
    runMutation (throw error : JuliaLean.base.array.MutationM E A) state =
      (Except.error error, state) := rfl

theorem aam_run_bind_success {E A B : Type} (m : JuliaLean.base.array.MutationM E A)
    (f : A → JuliaLean.base.array.MutationM E B) (before : MutableMemory E)
    (out : B) (after : MutableMemory E)
    (h : runMutation (m >>= f) before = (Except.ok out, after)) :
    ∃ value middle, runMutation m before = (Except.ok value, middle) ∧
      runMutation (f value) middle = (Except.ok out, after) := by
  rw [aam_run_bind] at h
  cases hfirst : runMutation m before with
  | mk result middle =>
    cases result with
    | error error => rw [hfirst] at h; cases h
    | ok value =>
      rw [hfirst] at h
      exact ⟨value, middle, rfl, h⟩


/-- Successful mapping preserves every observation preserved by each individual conversion. -/
theorem aam_mapMList_preserves {E R S O : Type}
    (f : R → JuliaLean.base.array.MutationM E S) (observe : MutableMemory E → O)
    (hf : ∀ value before out after,
      runMutation (f value) before = (.ok out, after) → observe after = observe before)
    (values : List R) (before after : MutableMemory E) (out : List S)
    (h : runMutation (mapMList f values) before = (.ok out, after)) :
    observe after = observe before := by
  induction values generalizing before after out with
  | nil =>
      rw [mapMList, aam_run_pure] at h
      have hs : before = after := congrArg Prod.snd h
      rw [← hs]
  | cons value values ih =>
      obtain ⟨converted, middle, hconverted, hrest⟩ :=
        aam_run_bind_success (f value)
          (fun converted => do
            let rest ← mapMList f values
            pure (converted :: rest)) before out after h
      obtain ⟨rest, final, hrest, hpure⟩ :=
        aam_run_bind_success (mapMList f values)
          (fun rest => pure (converted :: rest)) middle out after hrest
      rw [aam_run_pure] at hpure
      have hs : final = after := congrArg Prod.snd hpure
      rw [← hs]
      exact (ih middle final rest hrest).trans (hf value before converted middle hconverted)

/-- The dimension-tuple circshift branch is correct when transformed indices remain observable. -/
theorem aam_circshift_dims_with_index_closure (E A Ix : Type)
    (observation : ShiftObservation E A Ix)
    (similar : A → JuliaLean.base.array.MutationM E A)
    (circshiftBang : A → A → List (JInt .i64) → JuliaLean.base.array.MutationM E A)
    (a : A) (shifts : List (JInt .i64)) (state : MutableMemory E)
    (out : A) (final : MutableMemory E)
    (hsimilar : ∀ x dest before after,
      runMutation (similar x) before = (.ok dest, after) →
        ∀ ix ∈ observation.indices x,
          observation.contents after x ix = observation.contents before x ix)
    (hshift : ∀ dest src shifts before out final,
      runMutation (circshiftBang dest src shifts) before = (.ok out, final) →
        ∀ ix ∈ observation.indices src,
          observation.contents final out ix =
            observation.contents before src
              (observation.indexAt src
                (shiftedCoordinates (observation.coordinates ix) (observation.shape src)
                  (shifts.map fun x => x.val))))
    (hclosed : ∀ ix ∈ observation.indices a,
      observation.indexAt a (shiftedCoordinates (observation.coordinates ix)
        (observation.shape a) (shifts.map fun x => x.val)) ∈ observation.indices a)
    (h : runMutation (circshiftDims similar circshiftBang a shifts) state = (.ok out, final)) :
    ∀ ix ∈ observation.indices a,
      observation.contents final out ix =
        observation.contents state a
          (observation.indexAt a (shiftedCoordinates (observation.coordinates ix)
            (observation.shape a) (shifts.map fun x => x.val))) := by
  obtain ⟨dest, middle, hsimilarRun, hshiftRun⟩ :=
    aam_run_bind_success (similar a) (fun dest => circshiftBang dest a shifts) state out final h
  intro ix hix
  exact (hshift dest a shifts middle out final hshiftRun ix hix).trans
    (hsimilar a dest state middle hsimilarRun _ (hclosed ix hix))

/-- The messages of the inner (`true`) and outer (`false`) count checks. -/
def aamRepeatMessages {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A) (counts : CountArg C I) :
    Bool → String × String × (JInt .i64 → String)
  | true => ("repeat requires integer counts, got inner = " ++ ctx.showCounts counts,
      "no inner repetition count may be negative; got " ++ ctx.showCounts counts,
      fun n => "number of inner repetitions (" ++ toString n.val ++
        ") cannot be less than number of dimensions of input array (" ++
        toString (ctx.ndims a).val ++ ")")
  | false => ("repeat requires integer counts, got outer = " ++ ctx.showCounts counts,
      "no outer repetition count may be negative; got " ++ ctx.showCounts counts,
      fun n => "number of outer repetitions (" ++ toString n.val ++
        ") cannot be less than number of dimensions of input array (" ++
        toString (ctx.ndims a).val ++ ")")

/-- The count-validation block shared by the inner and outer repeat checks. -/
def aam_repeat_count_check {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A)
    (counts : CountArg C I) (checkLength isInner : Bool) : JuliaLean.base.array.MutationM α Unit := do
  if !(<- ctx.all (fun x => pure (ctx.isInteger x)) counts) then
    throw (.argument (aamRepeatMessages ctx a counts isInner).1)
  if <- ctx.any (fun x => pure (ctx.isNegative x)) counts then
    throw (.argument (aamRepeatMessages ctx a counts isInner).2.1)
  if (<- ctx.countLength counts) < ctx.ndims a then
    if checkLength then
      throw (.argument ((aamRepeatMessages ctx a counts isInner).2.2 (<- ctx.countLength counts)))

theorem aam_repeat_count_check_failure {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A)
    (state : MutableMemory α) (counts : CountArg C I) (checkLength : Bool)
    (isInner : Bool)
    (h : repeatCountFailure ctx a state counts checkLength) :
    ∃ message, runMutation (aam_repeat_count_check ctx a counts checkLength isInner)
      state = (.error (.argument message), state) := by
  dsimp only [repeatCountFailure] at h
  rcases h with ⟨hstate, hall | ⟨hall, hnstate, hnegative | ⟨hnegative, hcheck, n, hn, hlt⟩⟩⟩
  · have ha : runMutation (ctx.all (fun x => pure (ctx.isInteger x)) counts) state =
        (.ok false, state) := Prod.ext hall hstate
    refine ⟨(aamRepeatMessages ctx a counts isInner).1, ?_⟩
    simp only [aam_repeat_count_check, aam_run_bind, ha, Bool.not_false,
      ↓reduceIte, aam_run_throw, aam_run_pure]
  · have ha : runMutation (ctx.all (fun x => pure (ctx.isInteger x)) counts) state =
        (.ok true, state) := Prod.ext hall hstate
    have hb : runMutation (ctx.any (fun x => pure (ctx.isNegative x)) counts) state =
        (.ok true, state) := Prod.ext hnegative hnstate
    refine ⟨(aamRepeatMessages ctx a counts isInner).2.1, ?_⟩
    simp only [aam_repeat_count_check, aam_run_bind, ha, hb, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, aam_run_throw, aam_run_pure]
  · have ha : runMutation (ctx.all (fun x => pure (ctx.isInteger x)) counts) state =
        (.ok true, state) := Prod.ext hall hstate
    have hb : runMutation (ctx.any (fun x => pure (ctx.isNegative x)) counts) state =
        (.ok false, state) := Prod.ext hnegative hnstate
    refine ⟨(aamRepeatMessages ctx a counts isInner).2.2 n, ?_⟩
    simp only [aam_repeat_count_check, aam_run_bind, ha, hb, hn, hlt, hcheck,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, aam_run_throw, aam_run_pure]

theorem aam_repeat_count_check_valid {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A)
    (state : MutableMemory α) (counts : CountArg C I) (checkLength : Bool)
    (isInner : Bool)
    (h : repeatCountValid ctx a state counts) :
    runMutation (aam_repeat_count_check ctx a counts checkLength isInner)
      state = (.ok (), state) := by
  rcases h with ⟨ha, hb, n, hn, hge⟩
  have hnot : ¬ n < ctx.ndims a := by
    change ¬ n.val < (ctx.ndims a).val
    exact Int.not_lt.mpr hge
  simp only [aam_repeat_count_check, aam_run_bind, ha, hb, hn, hnot,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, aam_run_throw, aam_run_pure]

theorem aam_bind_ite {E A B : Type} (p : Prop) [Decidable p]
    (yes no : JuliaLean.base.array.MutationM E A)
    (next : A → JuliaLean.base.array.MutationM E B) :
    ((if p then yes else no) >>= next) =
      (if p then yes >>= next else no >>= next) := by
  split <;> rfl

theorem aam_throw_bind {E A B : Type} (error : Error)
    (next : A → JuliaLean.base.array.MutationM E B) :
    ((throw error : JuliaLean.base.array.MutationM E A) >>= next) = throw error := rfl

theorem aam_repeat_check_decompose {α A E C I Ix Selector : Type}
    (ctx : RepeatContext α A E C I Ix Selector) (a : A)
    (inner outer : Option (CountArg C I)) :
    RepeatInnerOuter.check ctx.requireOneBased ctx.isInteger ctx.isNegative ctx.all ctx.any
      ctx.countLength ctx.ndims ctx.showCounts a inner outer =
    (do
      if let some counts := inner then
        ctx.requireOneBased a
        aam_repeat_count_check ctx a counts true true
      if let some counts := outer then
        aam_repeat_count_check ctx a counts inner.isSome false) := by
  cases inner <;> cases outer <;>
    simp only [RepeatInnerOuter.check, aam_repeat_count_check, aamRepeatMessages,
      Option.isSome_some, Option.isSome_none, bind_assoc, aam_bind_ite, aam_throw_bind, pure_bind,
      bind_pure, ↓reduceIte]

/-- The validation half of RepeatFullSpec follows from its stated inspection hypotheses. -/
theorem aam_repeat_check_spec : JuliaLean.Proofs.base.abstractarraymath.RepeatCheckSpec := by
  intro α A E C I Ix Selector ctx a inner outer state hrequire hbad
  rw [aam_repeat_check_decompose]
  cases hi : inner with
  | none =>
      cases ho : outer with
      | none => simp only [hi, ho, false_or, false_and] at hbad
      | some counts =>
          simp only [hi, ho, Option.isSome_none, false_or, and_true] at hbad
          obtain ⟨message, hm⟩ := aam_repeat_count_check_failure ctx a state counts false false hbad
          simp only [hi, ho, Option.isSome_none, aam_run_bind, aam_run_pure, hm]
  | some counts =>
      have hr : runMutation (ctx.requireOneBased a) state = (.ok (), state) :=
        hrequire (by simp only [hi, Option.isSome_some])
      cases ho : outer with
      | none =>
          simp only [hi, ho, false_and, or_false] at hbad
          obtain ⟨message, hm⟩ := aam_repeat_count_check_failure ctx a state counts true true hbad
          simp only [hi, ho, aam_run_bind, aam_run_pure, hr, hm]
      | some outerCounts =>
          simp only [hi, ho, Option.isSome_some] at hbad
          rcases hbad with hf | ⟨hf, hv⟩
          · obtain ⟨message, hm⟩ := aam_repeat_count_check_failure ctx a state counts true true hf
            simp only [hi, ho, aam_run_bind, aam_run_pure, hr, hm]
          · have hm := aam_repeat_count_check_valid ctx a state counts true true hv
            obtain ⟨message, hoFail⟩ :=
              aam_repeat_count_check_failure ctx a state outerCounts true false hf
            simp only [hi, ho, Option.isSome_some, aam_run_bind, aam_run_pure, hr, hm, hoFail]


end JuliaLean.ChatGPT.Batch4.Group24


/-!
Finite diagnostics for missing interface assumptions. These are not claims about Julia bugs.
The frozen properties and their target theorem names are left unchanged and unfilled.
-/
namespace JuliaLean.ChatGPT.Batch4.Group24
open JuliaLean JuliaLean.base.array JuliaLean.base.abstractarraymath
open JuliaLean.Proofs.base.abstractarraymath

def aamFailingLength (_ : Unit) : Except Error (JInt .i64) := .error .bounds
def aamFailingReshape (_ : Unit) (_ : JInt .i64) : Except Error Unit := .error .bounds

theorem aam_vectorization_vacuous_premises :
    (∀ n, aamFailingLength () = .ok n → ∃ b, aamFailingReshape () n = .ok b) ∧
    (∀ n b, aamFailingReshape () n = .ok b →
      (Except.ok (int 0) : Except Error (JInt .i64)) = .ok n ∧ True) ∧
    ¬ (∃ b, vecArray aamFailingLength aamFailingReshape () = .ok b) := by
  constructor
  · intro n h
    cases h
  constructor
  · intro n b h
    cases h
  · intro ⟨b, h⟩
    cases h

def aamNeverShares (_ _ : Unit) : Prop := False

def aamEmptyDrop : Except Error Unit :=
  dropdimsDims (fun _ => []) (fun _ _ => .error .bounds)
    (fun _ : Unit => int 0) (fun _ _ => .ok ()) (fun _ => .ok (int 1))
    (fun _ => .ok ([] : List Unit)) (fun {S} _ (seed : S) _ => .ok seed)
    (fun _ => false) subTupleDispatch (fun _ => "") (fun _ xs => .ok xs)
    (fun _ _ => .ok ()) () []

theorem aam_empty_drop_missing_storage_law :
    aamEmptyDrop = .ok () ∧ ¬ aamNeverShares () () := ⟨rfl, id⟩

def aamEmptyInsert : Except Error Unit :=
  insertdimsDims (fun _ => []) (fun _ _ => .error .bounds) 0
    (fun _ : Unit => fun _ => .ok ()) (fun _ => ())
    (fun {S} _ (seed : S) _ => .ok seed) (fun _ _ => .ok ()) () []

theorem aam_empty_insert_missing_storage_law :
    aamEmptyInsert = .ok () ∧ ¬ aamNeverShares () () := ⟨rfl, id⟩

def aamUncheckedViewOps : SelectdimInterfaces Unit Unit Unit Unit Unit where
  axes _ := .ok [()]
  colon := ()
  setindex _ _ _ := [()]
  dimensionAtLeastOne _ := .ok true
  showDim _ := ""
  ndims _ := int 1
  dimensionGreater _ _ := .ok false
  indexEqualsOne _ := .ok true
  minusOne _ := .ok ()
  ntupleColons _ := .ok []
  boundsError _ _ := .bounds
  view _ _ := .ok ()
  dimensionToNat _ := 1
  oneDimensional _ := True
  isSlice _ := False
  viewInBounds _ _ := false

theorem aam_selectdim_missing_bounds_law :
    (∃ axes, aamUncheckedViewOps.axes () = .ok axes ∧
      aamUncheckedViewOps.setindex () () (axes.map fun _ => aamUncheckedViewOps.colon) =
        selectedIndices (aamUncheckedViewOps.ndims ()).val.toNat
          (aamUncheckedViewOps.dimensionToNat ()) () aamUncheckedViewOps.colon) ∧
    ¬ aamUncheckedViewOps.isSlice () ∧
    selectdim aamUncheckedViewOps.axes aamUncheckedViewOps.colon aamUncheckedViewOps.setindex
      (selectdimInternal aamUncheckedViewOps.dimensionAtLeastOne aamUncheckedViewOps.showDim
        aamUncheckedViewOps.ndims
        aamUncheckedViewOps.dimensionGreater aamUncheckedViewOps.indexEqualsOne
        aamUncheckedViewOps.minusOne aamUncheckedViewOps.ntupleColons
        aamUncheckedViewOps.boundsError aamUncheckedViewOps.view) () () () = .ok () ∧
    aamUncheckedViewOps.viewInBounds () () = false := by
  exact ⟨⟨[()], rfl, rfl⟩, id, rfl, rfl⟩

/-- Two observed locations, only one of which is protected by the frozen shift hypotheses. -/
def aamShiftObservation : ShiftObservation Nat Bool Bool where
  shape _ := [1]
  indices _ := [false]
  coordinates _ := [1]
  indexAt _ _ := true
  contents state array index :=
    if array then some state.arrays.length
    else if index then some state.memories.length else some 0

def aamShiftDummyArray : MutableVector := ⟨(0, int 1), int 0⟩

def aamShiftSimilar (_ : Bool) : JuliaLean.base.array.MutationM Nat Bool :=
  ExceptT.mk (fun state => (.ok true, { state with memories := [] :: state.memories }))

def aamShiftBang (_dest src : Bool) (_shifts : List (JInt .i64)) :
    JuliaLean.base.array.MutationM Nat Bool :=
  ExceptT.mk (fun state => (.ok true,
    { state with arrays := (List.replicate
        (if src then state.arrays.length else state.memories.length) aamShiftDummyArray) }))

theorem aam_shift_similar_preserves_observed :
    ∀ x dest before after,
      runMutation (aamShiftSimilar x) before = (.ok dest, after) →
        ∀ ix ∈ aamShiftObservation.indices x,
          aamShiftObservation.contents after x ix = aamShiftObservation.contents before x ix := by
  intro x dest before after h ix hix
  have hs : { before with memories := [] :: before.memories } = after := congrArg Prod.snd h
  have hi : ix = false := List.mem_singleton.mp hix
  rw [← hs, hi]
  cases x <;> rfl

theorem aam_shift_bang_obeys_stated_data_law :
    ∀ dest src shifts before out final,
      runMutation (aamShiftBang dest src shifts) before = (.ok out, final) →
        ∀ ix ∈ aamShiftObservation.indices src,
          aamShiftObservation.contents final out ix =
            aamShiftObservation.contents before src
              (aamShiftObservation.indexAt src
                (shiftedCoordinates (aamShiftObservation.coordinates ix)
                  (aamShiftObservation.shape src) (shifts.map fun x => x.val))) := by
  intro dest src shifts before out final h ix hix
  have ho : true = out := Except.ok.inj (congrArg Prod.fst h)
  have hs : { before with arrays := (List.replicate
      (if src then before.arrays.length else before.memories.length) aamShiftDummyArray) } = final :=
    congrArg Prod.snd h
  rw [← hs, ← ho]
  change some (List.replicate
      (if src then before.arrays.length else before.memories.length) aamShiftDummyArray).length = _
  rw [List.length_replicate]
  cases src <;> rfl

def aamShiftBefore : MutableMemory Nat := ⟨[], []⟩
def aamShiftAfter : MutableMemory Nat := ⟨[[]], [aamShiftDummyArray]⟩

theorem aam_shift_missing_index_closure :
    runMutation (circshiftDims aamShiftSimilar aamShiftBang false []) aamShiftBefore =
      (.ok true, aamShiftAfter) ∧
    false ∈ aamShiftObservation.indices false ∧
    aamShiftObservation.contents aamShiftAfter true false = some 1 ∧
    aamShiftObservation.contents aamShiftBefore false
      (aamShiftObservation.indexAt false (shiftedCoordinates
        (aamShiftObservation.coordinates false) (aamShiftObservation.shape false) [])) = some 0 ∧
    aamShiftObservation.indexAt false [] ∉ aamShiftObservation.indices false := by
  refine ⟨rfl, by decide, rfl, rfl, ?_⟩
  decide

/-- All arithmetic is ordinary Int arithmetic; the unregulated allocation callback is the defect. -/
def aamRepeatOps : RepeatArrayOps Unit Nat Unit Int Unit Unit where
  size _ := pure [1]
  sizeAt _ _ := pure 1
  length _ := pure 1
  similar1 _ _ := pure 1
  similar2 _ _ _ := pure 1
  similarDims _ _ := pure 1
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  checkedMul x y := pure (x * y)
  range _ _ := pure []
  rangeSelector _ _ := pure ()
  matrixIndex _ _ := ()
  vectorIndex _ := ()
  cartesianIndicesArray _ := pure []
  cartesianIndicesDims _ := pure []
  tupleIndex _ := []
  cartesianIndex _ := ()
  zipMap3 _ _ _ _ := []
  getindex _ _ := pure ()
  setindex _ _ _ := pure ()
  setBlock _ _ _ := pure ()

def aamRepeatContext : RepeatContext Unit Nat Unit Int Unit Unit Unit where
  arrayOps := aamRepeatOps
  rank _ := 1
  requireOneBased _ := pure ()
  isInteger _ := true
  isNegative n := decide (n < 0)
  all _ _ := pure true
  any _ _ := pure false
  countLength _ := pure (int 1)
  ndims _ := int 1
  showCounts _ := ""
  collect _ := pure []
  tuple := id
  fillToLength xs one n := xs ++ List.replicate (n - xs.length) one
  reshape _ _ := throw .bounds

def aamRepeatState : MutableMemory Unit := ⟨[], []⟩

def aamRepeatCheck := RepeatInnerOuter.checkDispatch
  aamRepeatContext.requireOneBased aamRepeatContext.isInteger aamRepeatContext.isNegative
  aamRepeatContext.all aamRepeatContext.any aamRepeatContext.countLength aamRepeatContext.ndims
  aamRepeatContext.showCounts

def aamRepeatResolve := RepeatInnerOuter.resolveDispatch
  aamRepeatContext.rank aamRepeatOps.size aamRepeatContext.collect aamRepeatContext.tuple
  aamRepeatContext.fillToLength aamRepeatOps.one aamRepeatContext.reshape

def aamRepeatExecute := RepeatInnerOuter.repeatInnerOuterDispatch aamRepeatOps aamRepeatContext.rank

theorem aam_repeat_reshape_premise_vacuous :
    ∀ a dims before reshaped after,
      runMutation (aamRepeatContext.reshape a dims) before = (.ok reshaped, after) →
        runMutation (aamRepeatOps.size reshaped) after = (.ok dims, after) := by
  intro a dims before reshaped after h
  change (Except.error Error.bounds, before) = (Except.ok reshaped, after) at h
  cases h

theorem aam_repeat_shape_missing_allocation_law :
    runMutation (aamRepeatOps.size 0) aamRepeatState = (.ok [1], aamRepeatState) ∧
    runMutation (aamRepeatCheck 0 (some (.tuple [2])) (some (.tuple [1]))) aamRepeatState =
      (.ok (), aamRepeatState) ∧
    runMutation (repeatKeyword
      (fun a inner outer => RepeatInnerOuter.repeatModule aamRepeatCheck aamRepeatResolve
        aamRepeatExecute a inner outer)
      0 (some (.tuple [2])) (some (.tuple [1]))) aamRepeatState = (.ok 1, aamRepeatState) ∧
    (runMutation (aamRepeatOps.size 1) aamRepeatState).1 = .ok [1] ∧
    expectedRepeatShape aamRepeatOps.one aamRepeatOps.mul [1] (some [2]) (some [1]) = [2] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def aamRepeatFailingAllocationOps : RepeatArrayOps Unit Nat Unit Int Unit Unit :=
  { aamRepeatOps with similarDims := fun _ _ => throw .bounds }

theorem aam_repeat_vector_missing_allocation_success :
    runMutation (aamRepeatFailingAllocationOps.length 0) aamRepeatState =
      (.ok (1 : Int), aamRepeatState) ∧
    runMutation
      (RepeatInnerOuter.repeatInnerOuterBoth
        (RepeatInnerOuter.repeatInner aamRepeatFailingAllocationOps)
        (RepeatInnerOuter.repeatOuterDispatch aamRepeatFailingAllocationOps (fun _ => 1))
        0 [1] [1]) aamRepeatState = (.error .bounds, aamRepeatState) := by
  exact ⟨rfl, rfl⟩


end JuliaLean.ChatGPT.Batch4.Group24

namespace JuliaLean.Proofs.base.abstractarraymath

open JuliaLean.Registry
def entries : List Entry := [
  { id := "aam-array-predicates", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["isreal(::AbstractArray)", "iszero(::AbstractArray)", "isreal(::AbstractArray{<:Real})"]
    statement := "Array isreal and iszero quantify the corresponding predicate over all elements; every real-element array is real."
    source := "base/abstractarraymath.jl:5-7"
    status := .proven, prop := ``ArrayPredicateSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.AamArrayPredicates },
  { id := "aam-vectorization", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["vec(::AbstractArray)", "vec(::AbstractVector)"]
    statement := "vec gives an array the one-dimensional shape of its length while sharing its storage, and returns an existing vector unchanged."
    source := "base/abstractarraymath.jl:11-42 (vec docstring)"
    status := .todo, prop := ``VectorizationSpec, thm := none, notes := "Prop allows length to fail while both callback premises hold vacuously, yet requires a successful vector result." },
  { id := "aam-dropdims", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["dropdims", "_dropdims(::AbstractArray,::Dims)", "_dropdims(::AbstractArray,::Integer)"]
    statement := "dropdims removes each requested singleton axis, rejects out-of-range, repeated, and non-singleton dimensions, and shares the input storage."
    source := "base/abstractarraymath.jl:48-104 (dropdims docstring and implementation)"
    status := .todo, prop := ``DropdimsSpec, thm := none, notes := "Prop leaves reshape, axes, storage and dimension enumeration unconstrained; even empty dimensions do not imply the promised shared storage." },
  { id := "aam-insertdims", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["insertdims", "_insertdims(::AbstractArray,::NTuple)", "_insertdims(::AbstractArray,::Integer)"]
    statement := "insertdims adds unique singleton axes at the requested positions, rejects positions outside 1:ndims(A)+length(dims), and shares the input storage."
    source := "base/abstractarraymath.jl:106-166 (insertdims docstring and implementation)"
    status := .todo, prop := ``InsertdimsSpec, thm := none, notes := "Prop does not connect successful reshape with output axes or shared storage, even for empty dimensions." },
  { id := "aam-elementwise", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj(::AbstractArray)", "real(::AbstractArray)", "imag(::AbstractArray)", "-(::AbstractArray)"]
    statement := "The conjugate, real, imaginary, and unary-negation array methods preserve shape and apply the corresponding scalar operation to each element."
    source := "base/abstractarraymath.jl:198-270, 293 (conj, real, imag docstrings and unary array operation)"
    status := .proven, prop := ``ArrayTransformSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.AamElementwise },
  { id := "aam-array-identities", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!(::AbstractArray{<:Real})", "conj(::AbstractArray{<:Real})", "real(::AbstractArray{<:Real})", "+(::AbstractArray{<:Number})", "*(::AbstractArray{<:Number,2})"]
    statement := "Real-array conjugation and real-part projection return the original array; unary plus and unary multiplication preserve their numeric array argument."
    source := "base/abstractarraymath.jl:195, 221, 246, 295-296"
    status := .proven, prop := ``ArrayIdentitySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.AamArrayIdentities },
  { id := "aam-imag-real-zero", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["imag(::AbstractArray{<:Real})"]
    statement := "The imaginary part of a real-element array is a zero array with the input shape."
    source := "base/abstractarraymath.jl:249-270 (imag docstring and real-array overload)"
    status := .proven, prop := ``ImaginaryRealArraySpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.AamImagRealZero },
  { id := "aam-conj-bang-numbers", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!(::AbstractArray{<:Number})"]
    statement := "conj! transforms each numeric element in place and returns the same array."
    source := "base/abstractarraymath.jl:172-194 (conj! docstring and numeric method)"
    status := .proven, prop := ``ConjBangNumbersSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.AamConjBangNumbers },
  { id := "aam-conj-bang-nested", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!(::AbstractArray)"]
    statement := "The generic conj! method applies conjugation to each element through conj! and returns the outer array."
    source := "base/abstractarraymath.jl:196"
    status := .proven, prop := ``ConjBangNestedSpec, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.AamConjBangNested },
  { id := "multidim-selectdim-in-range", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)"]
    statement := "For 1 ≤ d ≤ ndims(A) and a one-dimensional index i, selectdim(A,d,i) agrees with view(A, :, ..., i, ..., :) in size or exception."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring)"
    status := .proven, prop := ``SelectdimInRange, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.MultidimSelectdimInRange },
  { id := "multidim-selectdim-cartesian-oob", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)", "_selectdim"]
    statement := "Every position addressed by a successful selectdim view lies inside A."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring); invariant: views are bounds-checked"
    status := .todo, prop := ``SelectdimInBounds, thm := none, notes := "Prop does not relate successful view execution to its arbitrary viewInBounds observation, so the promised bounds conclusion can fail." },
  { id := "multidim-selectdim-trailing", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)", "_selectdim"]
    statement := "selectdim(A,d,i) agrees with view(A, :, ..., i, ..., :) for every d ≥ 1 and one-dimensional index i."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring)"
    status := .refuted, prop := ``SelectdimViewAgrees, thm := some ``JuliaLean.ChatGPT.Batch4.Group24.MultidimSelectdimTrailing , issue := "bugs/multidim-selectdim-trailing.yaml" },
  { id := "aam-circshift", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["circshift(::AbstractArray,::Real)", "circshift(::AbstractArray,::DimsInteger)", "circshift(::AbstractArray,shiftamt)"]
    statement := "circshift rotates each dimension by its shift amount, with missing shifts zero and wrapped indices."
    source := "base/abstractarraymath.jl:335-413 (circshift docstring and overloads)"
    status := .todo, prop := ``CircularShiftSpec, thm := none, notes := "Prop permits transformed coordinates outside the index set protected by its source-preservation premises; the coordinate promise needs index closure." },
  { id := "arrayops-repeat", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat(A::AbstractArray; inner, outer)", "repeat_inner", "repeat_outer(::AbstractVector)"]
    statement := "For a vector and nonnegative Int counts, inner repetition duplicates each entry consecutively, outer repetition duplicates the whole vector, and checked size products reject overflow."
    source := "base/abstractarraymath.jl:449-481 (repeat docstring), 573-612"
    status := .todo, prop := ``RepeatVectorSpec, thm := none, notes := "Prop permits a length-one count-one input to fail through the unconstrained allocator; the promised result needs allocation and element-access laws." },
  { id := "multidim-repeat-size", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat(A::AbstractArray; inner, outer)", "_RepeatInnerOuter.check", "_RepeatInnerOuter.resolve", "repeat_inner_outer", "repeat_inner", "repeat_outer"]
    statement := "repeat(A; inner, outer) pads sizes and counts to a common rank, multiplies dimensions componentwise, rejects negative counts and invalid ranks, and returns the repeated array."
    source := "base/abstractarraymath.jl:449-456 (repeat docstring) and lines 488-612"
    status := .todo, prop := ``RepeatFullSpec, thm := none, notes := "Prop omits allocation/shape laws: an unconstrained allocator may return shape [1] for a size-[1] input repeated with inner=[2], outer=[1]." }
]

/-! ## Method coverage

isreal@5 -> aam-array-predicates
iszero@6 -> aam-array-predicates
isreal@7 -> aam-array-predicates
vec@41 -> aam-vectorization
vec@42 -> aam-vectorization
_sub@44 -> nothing to promise
_sub@45 -> nothing to promise
_sub@46 -> nothing to promise
dropdims@85 -> aam-dropdims
_dropdims@86 -> aam-dropdims
_dropdims@104 -> aam-dropdims
insertdims@146 -> aam-insertdims
_insertdims@147 -> aam-insertdims
_insertdims@166 -> aam-insertdims
conj!@194 -> aam-conj-bang-numbers
conj!@195 -> aam-array-identities
conj!@196 -> aam-conj-bang-nested
conj@220 -> aam-elementwise
conj@221 -> aam-array-identities
real@245 -> aam-elementwise
real@246 -> aam-array-identities
imag@269 -> aam-elementwise
imag@270 -> aam-imag-real-zero
reim@291 -> declaration only; generic implementation is in base/complex.jl
unary -@293 -> aam-elementwise
unary +@295 -> aam-array-identities
unary *@296 -> aam-array-identities
selectdim@327 -> multidim-selectdim-in-range, multidim-selectdim-cartesian-oob, multidim-selectdim-trailing
_selectdim@328 -> multidim-selectdim-in-range, multidim-selectdim-cartesian-oob, multidim-selectdim-trailing
circshift@335 -> aam-circshift
circshift@338 -> aam-circshift
circshift@411 -> aam-circshift
repeat@445 -> nothing to promise
repeat@482 -> arrayops-repeat, multidim-repeat-size
_RepeatInnerOuter.repeat@488 -> multidim-repeat-size
to_tuple@494 -> multidim-repeat-size
to_tuple@495 -> multidim-repeat-size
to_tuple@496 -> multidim-repeat-size
pad@498 -> multidim-repeat-size
pad@502 -> multidim-repeat-size
resolve@507 -> multidim-repeat-size
resolve@510 -> multidim-repeat-size
resolve@514 -> multidim-repeat-size
resolve@517 -> multidim-repeat-size
resolve@521 -> multidim-repeat-size
check@526 -> aam-repeat-checks
repeat_inner_outer@554 -> multidim-repeat-size
repeat_inner_outer@555 -> multidim-repeat-size
repeat_inner_outer@556 -> multidim-repeat-size
repeat_inner_outer@557 -> multidim-repeat-size
repeat_outer@559 -> multidim-repeat-size
repeat_outer@573 -> arrayops-repeat, multidim-repeat-size
repeat_outer@583 -> multidim-repeat-size
repeat_inner@599 -> arrayops-repeat, multidim-repeat-size
-/
/-! Nothing to promise: `_sub`@44-46 is the private tuple-tail helper used by dropdims' concrete-axis type assertion; its public effect is covered by `aam-dropdims`.

Nothing to promise: `dropdims`@85 and `insertdims`@146 only forward to the checked implementations listed above.

Nothing to promise: `repeat`@445 forwards positional counts to the keyword method; the repeated-result contract is stated for `_RepeatInnerOuter.repeat`.

`reim`@291 is a function declaration without a method body in this file. Its executable generic method is modelled in `JuliaLean.base.complex`.
-/

end JuliaLean.Proofs.base.abstractarraymath
