import JuliaLean.base.abstractarraymath
import JuliaLean.base.array
import JuliaLean.Registry.Types

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
    conjRealArray a = a ∧ realRealArray a = a ∧
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
      (selectdimInternal ops.dimensionAtLeastOne ops.ndims ops.dimensionGreater
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
      (selectdimInternal ops.dimensionAtLeastOne ops.ndims ops.dimensionGreater
        ops.indexEqualsOne ops.minusOne ops.ntupleColons ops.boundsError ops.view)
      a d i = ops.view a (selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon)

def SelectdimInBounds : Prop :=
  ∀ (A D Ix Ax V : Type) (ops : SelectdimInterfaces A D Ix Ax V) (a : A) (d : D) (i : Ix),
    (∃ axes, ops.axes a = .ok axes ∧
      ops.setindex i d (axes.map fun _ => ops.colon) =
        selectedIndices (ops.ndims a).val.toNat (ops.dimensionToNat d) i ops.colon) →
    ¬ ops.isSlice i →
    match selectdim ops.axes ops.colon ops.setindex
      (selectdimInternal ops.dimensionAtLeastOne ops.ndims ops.dimensionGreater
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
      ctx.all ctx.any ctx.countLength ctx.ndims
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
        ctx.all ctx.any ctx.countLength ctx.ndims a inner outer) state).1 with
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

def entries : List Entry := [
  { id := "aam-array-predicates", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["isreal(::AbstractArray)", "iszero(::AbstractArray)", "isreal(::AbstractArray{<:Real})"]
    statement := "Array isreal and iszero quantify the corresponding predicate over all elements; every real-element array is real."
    source := "base/abstractarraymath.jl:5-7"
    status := .todo, prop := ``ArrayPredicateSpec, thm := none },
  { id := "aam-vectorization", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["vec(::AbstractArray)", "vec(::AbstractVector)"]
    statement := "vec gives an array the one-dimensional shape of its length while sharing its storage, and returns an existing vector unchanged."
    source := "base/abstractarraymath.jl:11-42 (vec docstring)"
    status := .todo, prop := ``VectorizationSpec, thm := none },
  { id := "aam-dropdims", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["dropdims", "_dropdims(::AbstractArray,::Dims)", "_dropdims(::AbstractArray,::Integer)"]
    statement := "dropdims removes each requested singleton axis, rejects out-of-range, repeated, and non-singleton dimensions, and shares the input storage."
    source := "base/abstractarraymath.jl:48-104 (dropdims docstring and implementation)"
    status := .todo, prop := ``DropdimsSpec, thm := none },
  { id := "aam-insertdims", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["insertdims", "_insertdims(::AbstractArray,::NTuple)", "_insertdims(::AbstractArray,::Integer)"]
    statement := "insertdims adds unique singleton axes at the requested positions, rejects positions outside 1:ndims(A)+length(dims), and shares the input storage."
    source := "base/abstractarraymath.jl:106-166 (insertdims docstring and implementation)"
    status := .todo, prop := ``InsertdimsSpec, thm := none },
  { id := "aam-elementwise", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj(::AbstractArray)", "real(::AbstractArray)", "imag(::AbstractArray)", "-(::AbstractArray)"]
    statement := "The conjugate, real, imaginary, and unary-negation array methods preserve shape and apply the corresponding scalar operation to each element."
    source := "base/abstractarraymath.jl:198-270, 293 (conj, real, imag docstrings and unary array operation)"
    status := .todo, prop := ``ArrayTransformSpec, thm := none },
  { id := "aam-array-identities", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!(::AbstractArray{<:Real})", "conj(::AbstractArray{<:Real})", "real(::AbstractArray{<:Real})", "+(::AbstractArray{<:Number})", "*(::AbstractArray{<:Number,2})"]
    statement := "Real-array conjugation and real-part projection return the original array; unary plus and unary multiplication preserve their numeric array argument."
    source := "base/abstractarraymath.jl:195, 221, 246, 295-296"
    status := .todo, prop := ``ArrayIdentitySpec, thm := none },
  { id := "aam-imag-real-zero", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["imag(::AbstractArray{<:Real})"]
    statement := "The imaginary part of a real-element array is a zero array with the input shape."
    source := "base/abstractarraymath.jl:249-270 (imag docstring and real-array overload)"
    status := .todo, prop := ``ImaginaryRealArraySpec, thm := none },
  { id := "aam-conj-bang-numbers", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!(::AbstractArray{<:Number})"]
    statement := "conj! transforms each numeric element in place and returns the same array."
    source := "base/abstractarraymath.jl:172-194 (conj! docstring and numeric method)"
    status := .todo, prop := ``ConjBangNumbersSpec, thm := none },
  { id := "aam-conj-bang-nested", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["conj!(::AbstractArray)"]
    statement := "The generic conj! method applies conjugation to each element through conj! and returns the outer array."
    source := "base/abstractarraymath.jl:196"
    status := .todo, prop := ``ConjBangNestedSpec, thm := none },
  { id := "multidim-selectdim-in-range", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)"]
    statement := "For 1 ≤ d ≤ ndims(A) and a one-dimensional index i, selectdim(A,d,i) agrees with view(A, :, ..., i, ..., :) in size or exception."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring)"
    status := .todo, prop := ``SelectdimInRange, thm := none },
  { id := "multidim-selectdim-cartesian-oob", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)", "_selectdim"]
    statement := "Every position addressed by a successful selectdim view lies inside A."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring); invariant: views are bounds-checked"
    status := .todo, prop := ``SelectdimInBounds, thm := none },
  { id := "multidim-selectdim-trailing", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["selectdim(A::AbstractArray, d::Integer, i)", "_selectdim"]
    statement := "selectdim(A,d,i) agrees with view(A, :, ..., i, ..., :) for every d ≥ 1 and one-dimensional index i."
    source := "base/abstractarraymath.jl:300-305 (selectdim docstring)"
    status := .todo, prop := ``SelectdimViewAgrees, thm := none },
  { id := "aam-circshift", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["circshift(::AbstractArray,::Real)", "circshift(::AbstractArray,::DimsInteger)", "circshift(::AbstractArray,shiftamt)"]
    statement := "circshift rotates each dimension by its shift amount, with missing shifts zero and wrapped indices."
    source := "base/abstractarraymath.jl:335-413 (circshift docstring and overloads)"
    status := .todo, prop := ``CircularShiftSpec, thm := none },
  { id := "arrayops-repeat", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat(A::AbstractArray; inner, outer)", "repeat_inner", "repeat_outer(::AbstractVector)"]
    statement := "For a vector and nonnegative Int counts, inner repetition duplicates each entry consecutively, outer repetition duplicates the whole vector, and checked size products reject overflow."
    source := "base/abstractarraymath.jl:449-481 (repeat docstring), 573-612"
    status := .todo, prop := ``RepeatVectorSpec, thm := none },
  { id := "aam-repeat-checks", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["_RepeatInnerOuter.check"]
    statement := "The repeat count checker rejects non-integer or negative counts and count lists shorter than the required rank."
    source := "base/abstractarraymath.jl:526-554"
    status := .todo, prop := ``RepeatCheckSpec, thm := none },
  { id := "multidim-repeat-size", juliaFile := "base/abstractarraymath.jl"
    juliaFns := ["repeat(A::AbstractArray; inner, outer)", "_RepeatInnerOuter.check", "_RepeatInnerOuter.resolve", "repeat_inner_outer", "repeat_inner", "repeat_outer"]
    statement := "repeat(A; inner, outer) pads sizes and counts to a common rank, multiplies dimensions componentwise, rejects negative counts and invalid ranks, and returns the repeated array."
    source := "base/abstractarraymath.jl:449-456 (repeat docstring) and lines 488-612"
    status := .todo, prop := ``RepeatFullSpec, thm := none }
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
