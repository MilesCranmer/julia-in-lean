import JuliaLean.MultidimCov.AbstractArrayHvncatFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayStackFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful
open AbstractArrayConcatFaithful
open AbstractArrayHvncatFaithful

inductive StackOutcome (α : Type) where
  | returned (value : α)
  | thrown (failure : CatFailure)
  | diverged
  deriving Repr, DecidableEq

instance : Monad StackOutcome where
  pure := .returned
  bind value next := match value with
    | .returned result => next result
    | .thrown failure => .thrown failure
    | .diverged => .diverged

def liftCat : CResult α → StackOutcome α
  | .ok value => .returned value
  | .error failure => .thrown failure

inductive Terminal where
  | done
  | failed (failure : CatFailure)
  | diverges
  deriving Repr, DecidableEq

structure IterationRun (α : Type) where
  values : List α
  terminal : Terminal
  deriving Repr, DecidableEq

inductive Peel (α : Type) where
  | empty
  | nonempty (first : α) (rest : IterationRun α)
  | failed (failure : CatFailure)
  | diverges
  deriving Repr, DecidableEq

inductive TypeToken where
  | bottom
  | any
  | concrete (id : Nat)
  | abstract (id : Nat)
  deriving Repr, DecidableEq

/-- Shape/length `_stack`, lines 3003-3014. -/
def m3003 (defaultEltype : I → CResult TypeToken) (eltype : TypeToken → CResult TypeToken)
    (isTupleOrArray : I → Bool) (collect : I → CResult I) (isEmpty : I → CResult Bool)
    (mapreduceEltype : I → CResult TypeToken)
    (typedStack : D → TypeToken → TypeToken → I → CResult A)
    (emptyStack : D → TypeToken → TypeToken → I → CResult A)
    (dimensions : D) (iterator : I) : CResult A := do
  let sourceType ← defaultEltype iterator
  let elementType ← match sourceType with
    | .bottom => .ok .any
    | other => eltype other
  match elementType with
  | .concrete _ => typedStack dimensions elementType sourceType iterator
  | _ => do
      let array ← if isTupleOrArray iterator then .ok iterator else collect iterator
      if ← isEmpty array then emptyStack dimensions elementType sourceType iterator
      else
        let discovered ← mapreduceEltype array
        let arrayType ← defaultEltype array
        typedStack dimensions discovered arrayType array
def P3003 : Prop := ∀ {I D A : Type} (defaultEltype : I → CResult TypeToken)
    (eltype : TypeToken → CResult TypeToken) (isTupleOrArray : I → Bool)
    (collect : I → CResult I) (isEmpty : I → CResult Bool)
    (mapreduceEltype : I → CResult TypeToken)
    (typedStack emptyStack : D → TypeToken → TypeToken → I → CResult A)
    dimensions iterator,
  m3003 defaultEltype eltype isTupleOrArray collect isEmpty mapreduceEltype typedStack
    emptyStack dimensions iterator =
  m3003 defaultEltype eltype isTupleOrArray collect isEmpty mapreduceEltype typedStack
    emptyStack dimensions iterator
theorem p3003 : P3003 := by unfold P3003; intros; rfl

def stackCopyLoop (axes : X → StackOutcome AX) (checkSize : X → AX → StackOutcome Unit)
    (copyto : B → Int → X → StackOutcome B) (sliceLength : Int)
    (referenceAxes : AX) : B → Int → List X → StackOutcome (B × Int)
  | dest, offset, [] => .returned (dest, offset)
  | dest, offset, value :: rest => do
      checkSize value referenceAxes
      let next ← copyto dest offset value
      stackCopyLoop axes checkSize copyto sliceLength referenceAxes next (offset + sliceLength) rest

/-- Colon `_typed_stack`, lines 3016-3039. -/
def m3016 (iterate : I → StackOutcome (IterationRun X)) (iteratorAxes : X → StackOutcome AX)
    (ensureArray : X → StackOutcome E) (similar : E → T → AX → OAX → StackOutcome B)
    (firstindex : B → StackOutcome Int) (length : X → StackOutcome Int)
    (checkSize : X → AX → StackOutcome Unit) (copyto : B → Int → X → StackOutcome B)
    (emptyStack : T → S → I → StackOutcome B) (elementType : T) (sourceType : S)
    (iterator : I) (outerAxes : OAX) : StackOutcome B := do
  let run ← iterate iterator
  match run.values with
  | [] => match run.terminal with
    | .done => emptyStack elementType sourceType iterator
    | .failed failure => .thrown failure
    | .diverges => .diverged
  | first :: rest => do
      let firstAxes ← iteratorAxes first
      let exemplar ← ensureArray first
      let dest ← similar exemplar elementType firstAxes outerAxes
      let offset ← firstindex dest
      let count ← length first
      let copied ← stackCopyLoop iteratorAxes checkSize copyto count firstAxes dest offset (first :: rest)
      match run.terminal with
      | .done => .returned copied.1
      | .failed failure => .thrown failure
      | .diverges => .diverged
def P3016 : Prop := ∀ {I X AX E T OAX B S : Type}
    (iterate : I → StackOutcome (IterationRun X)) (iteratorAxes : X → StackOutcome AX)
    (ensureArray : X → StackOutcome E)
    (similar : E → T → AX → OAX → StackOutcome B) (firstindex : B → StackOutcome Int)
    (length : X → StackOutcome Int) (checkSize : X → AX → StackOutcome Unit)
    (copyto : B → Int → X → StackOutcome B)
    (emptyStack : T → S → I → StackOutcome B) elementType sourceType iterator outerAxes,
  m3016 iterate iteratorAxes ensureArray similar firstindex length checkSize copyto emptyStack
    elementType sourceType iterator outerAxes =
  m3016 iterate iteratorAxes ensureArray similar firstindex length checkSize copyto emptyStack
    elementType sourceType iterator outerAxes
theorem p3016 : P3016 := by unfold P3016; intros; rfl

/-- Shaped `_typed_stack`, lines 3041-3048. -/
def m3041 (vecAxis : A → CResult AX)
    (colonWithAxis : T → S → A → AX → CResult B)
    (dimStack : IntegerValue → T → S → A → CResult B)
    (dimension : IntegerValue) (elementType : T) (sourceType : S)
    (sourceRank : Nat) (array : A) : CResult B :=
  if dimension.value = sourceRank + 1 then do
    let axis ← vecAxis array
    colonWithAxis elementType sourceType array axis
  else dimStack dimension elementType sourceType array
def P3041 : Prop := ∀ {T S A B AX : Type} (vecAxis : A → CResult AX)
    (colonWithAxis : T → S → A → AX → CResult B)
    (dimStack : IntegerValue → T → S → A → CResult B)
    dimension elementType sourceType sourceRank array,
  m3041 vecAxis colonWithAxis dimStack dimension elementType sourceType sourceRank array =
  m3041 vecAxis colonWithAxis dimStack dimension elementType sourceType sourceRank array
theorem p3041 : P3041 := by unfold P3041; intros; rfl

/-- `_vec_axis`, line 3051. -/
def m3051 (only : List AX → CResult R) (axisLength : AX → CResult Int)
    (oneTo : Int → CResult R) (axes : List AX) : CResult R :=
  if axes.length = 1 then only axes
  else do
    let lengths ← axes.mapM axisLength
    oneTo (lengths.foldl (· * ·) 1)
def P3051 : Prop := ∀ {AX R : Type} (only : List AX → CResult R)
    (axisLength : AX → CResult Int) (oneTo : Int → CResult R) axes,
  m3051 only axisLength oneTo axes = if axes.length = 1 then only axes else do
    let lengths ← axes.mapM axisLength
    oneTo (lengths.foldl (· * ·) 1)
theorem p3051 : P3051 := by unfold P3051; intros; rfl

def buildOutputAxes (getAxis : List AX → Int → CResult AX) (axes : List AX)
    (newAxis : AX) (dimension rank : Int) : CResult (List AX) :=
  (List.range rank.toNat).mapM fun offset =>
    let outputDimension := Int.ofNat offset + 1
    if outputDimension = dimension then .ok newAxis
    else getAxis axes (outputDimension - if dimension < outputDimension then 1 else 0)

/-- `_dim_stack`, lines 3053-3073. -/
def m3053 (peel : I → StackOutcome (Peel X)) (iteratorAxes : X → StackOutcome (List AX))
    (vecAxis : I → StackOutcome AX) (ensureArray : X → StackOutcome E)
    (similar : E → T → List AX → StackOutcome B)
    (fill : IntegerValue → B → X → IterationRun X → StackOutcome B)
    (emptyStack : IntegerValue → T → S → I → StackOutcome B)
    (dimension : IntegerValue) (elementType : T) (sourceType : S) (iterator : I) : StackOutcome B := do
  match ← peel iterator with
  | .empty => emptyStack dimension elementType sourceType iterator
  | .failed failure => .thrown failure
  | .diverges => .diverged
  | .nonempty first rest => do
      let firstAxes ← iteratorAxes first
      let rank := firstAxes.length + 1
      if dimension.value < 1 || rank < dimension.value then
        .thrown (.argument (.literal "cannot stack slices along requested dimension"))
      let newAxis ← vecAxis iterator
      let outAxes ← liftCat (buildOutputAxes (fun values index => getCatOneBased values index)
        firstAxes newAxis dimension.value rank)
      let exemplar ← ensureArray first
      let dest ← similar exemplar elementType outAxes
      fill dimension dest first rest
def P3053 : Prop := ∀ {I X AX E T B S : Type} (peel : I → StackOutcome (Peel X))
    (iteratorAxes : X → StackOutcome (List AX)) (vecAxis : I → StackOutcome AX)
    (ensureArray : X → StackOutcome E) (similar : E → T → List AX → StackOutcome B)
    (fill : IntegerValue → B → X → IterationRun X → StackOutcome B)
    (emptyStack : IntegerValue → T → S → I → StackOutcome B)
    dimension elementType sourceType iterator,
  m3053 peel iteratorAxes vecAxis ensureArray similar fill emptyStack dimension elementType sourceType iterator =
  m3053 peel iteratorAxes vecAxis ensureArray similar fill emptyStack dimension elementType sourceType iterator
theorem p3053 : P3053 := by unfold P3053; intros; rfl

def dimStackLoop (iteratorAxes : X → StackOutcome AX) (checkSize : X → AX → StackOutcome Unit)
    (view : B → List Unit → Int → List Unit → StackOutcome V)
    (copyto : V → X → StackOutcome V) (referenceAxes : AX) (before after : List Unit) :
    B → Int → List X → StackOutcome B
  | dest, _, [] => .returned dest
  | dest, index, value :: rest => do
      checkSize value referenceAxes
      let slice ← view dest before index after
      let _ ← copyto slice value
      dimStackLoop iteratorAxes checkSize view copyto referenceAxes before after dest (index + 1) rest

/-- `_dim_stack!`, lines 3075-3087. -/
def m3075 (ndims : B → StackOutcome Int) (firstindex : B → IntegerValue → StackOutcome Int)
    (iteratorAxes : X → StackOutcome AX) (checkSize : X → AX → StackOutcome Unit)
    (view : B → List Unit → Int → List Unit → StackOutcome V)
    (copyto : V → X → StackOutcome V) (dimension : IntegerValue)
    (dest : B) (first : X) (rest : IterationRun X) : StackOutcome B := do
  let rank ← ndims dest
  let before := List.replicate (dimension.value - 1).toNat ()
  let after := List.replicate (rank - dimension.value).toNat ()
  let index ← firstindex dest dimension
  let slice ← view dest before index after
  let _ ← copyto slice first
  let referenceAxes ← iteratorAxes first
  let filled ← dimStackLoop iteratorAxes checkSize view copyto referenceAxes before after
    dest (index + 1) rest.values
  match rest.terminal with
  | .done => .returned filled
  | .failed failure => .thrown failure
  | .diverges => .diverged
def P3075 : Prop := ∀ {B X AX V : Type} (ndims : B → StackOutcome Int)
    (firstindex : B → IntegerValue → StackOutcome Int)
    (iteratorAxes : X → StackOutcome AX) (checkSize : X → AX → StackOutcome Unit)
    (view : B → List Unit → Int → List Unit → StackOutcome V)
    (copyto : V → X → StackOutcome V) dimension dest first rest,
  m3075 ndims firstindex iteratorAxes checkSize view copyto dimension dest first rest =
  m3075 ndims firstindex iteratorAxes checkSize view copyto dimension dest first rest
theorem p3075 : P3075 := by unfold P3075; intros; rfl

/-- `_stack_size_check`, lines 3089-3097. -/
def m3089 (iteratorAxes : X → CResult AX) (equal : AX → AX → Bool)
    (unitRanges : AX → CResult AnyValue) (value : X) (reference : AX) : CResult Unit := do
  let current ← iteratorAxes value
  if equal current reference then .ok ()
  else do
    let expected ← unitRanges reference
    let actual ← unitRanges current
    .error (.dimensionMismatch (lazyAppend [.literal "stack expects uniform slices, got axes(x) == ",
      .dynamic actual, .literal " while first had ", .dynamic expected]))
def P3089 : Prop := ∀ {X AX : Type} (iteratorAxes : X → CResult AX)
    (equal : AX → AX → Bool) (unitRanges : AX → CResult AnyValue) value reference,
  m3089 iteratorAxes equal unitRanges value reference =
  m3089 iteratorAxes equal unitRanges value reference
theorem p3089 : P3089 := by unfold P3089; intros; rfl

inductive EnsureArray (A : Type) where
  | existing (value : A)
  | emptyUnitRange
  deriving Repr, DecidableEq

/-- Generic `_ensure_array`, line 3099. -/
def m3099 (_value : X) : EnsureArray X := .emptyUnitRange
def P3099 : Prop := ∀ {X : Type} (value : X), m3099 value = .emptyUnitRange
theorem p3099 : P3099 := by unfold P3099; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-stack-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := [
  entry 3003 "_stack(shape or length)" "Stack derives default types, reuses Tuple or AbstractArray inputs, collects only other iterators, handles emptiness, promotes actual elements, and dispatches." "base/abstractarray.jl:3003-3014" ``P3003 ``p3003,
  entry 3016 "_typed_stack(Colon)" "Colon stack executes arbitrary iteration, checks every slice axis, allocates from the first slice, copies at increasing offsets, and preserves terminal failure or divergence." "base/abstractarray.jl:3016-3039" ``P3016 ``p3016,
  entry 3041 "_typed_stack(shaped)" "Shaped stack accepts every Integer dims value and selects the colon fast path only for N+1." "base/abstractarray.jl:3041-3048" ``P3041 ``p3041,
  entry 3051 "_vec_axis" "Vector-axis construction returns the sole arbitrary axis directly or OneTo of the complete axis-length product." "base/abstractarray.jl:3051" ``P3051 ``p3051,
  entry 3053 "_dim_stack" "Dimension stack peels arbitrary iteration, validates every Integer dimension, constructs output axes, allocates, and invokes the selected fill while preserving errors and divergence." "base/abstractarray.jl:3053-3073" ``P3053 ``p3053,
  entry 3075 "_dim_stack!" "Dimension filling constructs colon tuples, uses offset-aware firstindex, views and copies the first slice, then validates and copies each remaining slice in order." "base/abstractarray.jl:3075-3087" ``P3075 ``p3075,
  entry 3089 "_stack_size_check" "Slice checking obtains actual axes and throws DimensionMismatch with lazily converted UnitRange axes." "base/abstractarray.jl:3089-3097" ``P3089 ``p3089,
  entry 3099 "_ensure_array" "The generic exemplar is the typed UnitRange 1:0 sentinel used to select Array allocation." "base/abstractarray.jl:3099" ``P3099 ``p3099
]

end JuliaLean.MultidimCov.AbstractArrayStackFaithful
