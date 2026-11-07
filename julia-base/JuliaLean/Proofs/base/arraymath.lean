import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.arraymath
import JuliaLean.Registry.Types
import JuliaLean.Proofs.base.arraymath.array_transforms

namespace JuliaLean.Proofs.base.arraymath

open JuliaLean.Registry
open JuliaLean.base.arraymath

abbrev Result := JuliaLean.base.abstractarray.Result
abbrev I64 := JuliaLean.base.abstractarray.I64
abbrev Effect (σ : Type) := StateT σ Result

/-- Read a value after a stateful array action, ignoring the unchanged store result. -/
def stateValue {σ α : Type} (action : Effect σ α) (state : σ) : Option α :=
  match StateT.run action state with
  | .ok (value, _) => some value
  | .error _ => none

/-- The pointwise contract of Julia's unary `map` on arrays. -/
def UnaryMapLaw {A R V : Type}
    (map : (V → Result V) → A → Result R)
    (get : A → I64 → Result V) (getResult : R → I64 → Result V) : Prop :=
  ∀ (f : V → Result V) (a : A) (r : R) (i : I64) (x y : V),
    map f a = .ok r → get a i = .ok x → f x = .ok y → getResult r i = .ok y

/-- The pointwise contract of Julia's multi-array `map` for equal-rank arrays. -/
def BinaryMapLaw {A R V F : Type}
    (map : F → A → A → List A → Result R)
    (get : A → I64 → Result V) (getResult : R → I64 → Result V)
    (apply : F → V → V → Result V) : Prop :=
  ∀ (f : F) (a b : A) (cs : List A) (r : R) (i : I64) (x y z : V),
    map f a b cs = .ok r → get a i = .ok x → get b i = .ok y →
    apply f x y = .ok z → getResult r i = .ok z

def valuesAt {A V : Type} (get : A → I64 → Result V) (i : I64) :
    List A → Result (List V)
  | [] => .ok []
  | array :: arrays => do
      let value ← get array i
      let rest ← valuesAt get i arrays
      pure (value :: rest)

def VariadicMapLaw {A R V F : Type}
    (map : F → A → A → List A → Result R)
    (get : A → I64 → Result V) (getResult : R → I64 → Result V)
    (apply : F → V → V → List V → Result V) : Prop :=
  ∀ (f : F) (a b : A) (cs : List A) (r : R) (i : I64)
    (x y z : V) (xs : List V),
    map f a b cs = .ok r → get a i = .ok x → get b i = .ok y →
    valuesAt get i cs = .ok xs → apply f x y xs = .ok z → getResult r i = .ok z

def ManyArrayMapLaw {A R V F : Type}
    (map : F → List A → Result R) (get : A → I64 → Result V)
    (getResult : R → I64 → Result V) (apply : F → List V → Result V) : Prop :=
  ∀ (f : F) (arrays : List A) (r : R) (i : I64) (values : List V) (result : V),
    map f arrays = .ok r → valuesAt get i arrays = .ok values →
    apply f values = .ok result → getResult r i = .ok result

def BinaryBroadcastLaw {A B R V F : Type}
    (broadcast : F → A → B → Result R)
    (getA : A → I64 → Result V) (getB : B → I64 → Result V)
    (getResult : R → I64 → Result V) (apply : F → V → V → Result V) : Prop :=
  ∀ (f : F) (a : A) (b : B) (r : R) (i : I64) (x y z : V),
    broadcast f a b = .ok r → getA a i = .ok x → getB b i = .ok y →
    apply f x y = .ok z → getResult r i = .ok z


/-- Axis endpoints supplied by a well-formed AbstractArray axis tuple. -/
def AxisEndpoints {m : Type → Type} {A Axis : Type} (ops : ArrayIndexOps m A Axis)
    (axes : List Axis) (firsts lasts : List I64) : Prop :=
  axes.length = firsts.length ∧ axes.length = lasts.length ∧
  ∀ k, k < axes.length →
    match axes[k]?, firsts[k]?, lasts[k]? with
    | some axis, some first, some last =>
        ops.first axis = .ok first ∧ ops.last axis = .ok last
    | _, _, _ => False

/-- AbstractArray axes enumerate every integer from their first through last index. -/
def AxisIndexRangeLaw {m : Type → Type} {A Axis : Type}
    (ops : ArrayIndexOps m A Axis) : Prop :=
  ∀ axis first last, ops.first axis = .ok first → ops.last axis = .ok last →
    ops.indices axis = JuliaLean.base.array.intRange first last

/-- `size` records the number of indices in every array axis. -/
def ReverseSizeLaw {Store A V Axis : Type}
    (ops : ReverseOps (Effect Store) A V Axis) : Prop :=
  ∀ array axes sizes,
    ops.index.axes array = .ok axes →
    ops.size array = .ok sizes →
    sizes.length = axes.length ∧
    ∀ k, k < axes.length →
      match axes[k]?, sizes[k]? with
      | some axis, some extent =>
          extent.val = Int.ofNat (ops.index.indices axis).length
      | _, _ => False

/-- Positive `Int` extents divide by two with Julia's integer division. -/
def ReverseDivideLaw {Store A V Axis : Type}
    (ops : ReverseOps (Effect Store) A V Axis) : Prop :=
  ∀ extent half state,
    0 ≤ extent.val →
    StateT.run (ops.divide extent (JuliaLean.base.abstractarray.int 2)) state =
      .ok (half, state) →
    half.val = extent.val / 2

/-- A view has the requested axes, shares selected values and writes with its source. -/
def ReverseViewLaw {Store A V Axis : Type}
    (ops : ReverseOps (Effect Store) A V Axis) : Prop :=
  ∀ array viewAxes view state state',
    StateT.run (ops.view array viewAxes) state = .ok (view, state') →
    (∀ axes, ops.index.axes view = .ok axes →
      axes.map ops.index.indices = viewAxes) ∧
    (∀ index value, index ∈ cartesianIndices viewAxes →
      StateT.run (ops.getindex array index) state = .ok (value, state) →
      StateT.run (ops.getindex array index) state' = .ok (value, state') ∧
      StateT.run (ops.getindex view index) state' = .ok (value, state')) ∧
    (∀ writeIndex newValue finalState,
      writeIndex ∈ cartesianIndices viewAxes →
      StateT.run (ops.setindex view writeIndex newValue) state' =
        .ok ((), finalState) →
      (∀ index value, index ∈ cartesianIndices viewAxes →
        StateT.run (ops.getindex array index) state = .ok (value, state) →
        (index = writeIndex →
          StateT.run (ops.getindex array index) finalState = .ok (newValue, finalState)) ∧
        (index ≠ writeIndex →
          StateT.run (ops.getindex array index) finalState = .ok (value, finalState))) ∧
      (∀ index value, index ∉ cartesianIndices viewAxes →
        StateT.run (ops.getindex array index) state = .ok (value, state) →
        StateT.run (ops.getindex array index) finalState = .ok (value, finalState)))
def ReverseOpsLaws {Store A V Axis : Type}
    (ops : ReverseOps (Effect Store) A V Axis) : Prop :=
  AxisIndexRangeLaw ops.index ∧
  ReverseSizeLaw ops ∧
  ReverseDivideLaw ops ∧
  (∀ array indices value state state',
    StateT.run (ops.getindex array indices) state = .ok (value, state') →
    state' = state) ∧
  (∀ array indices value state state',
    StateT.run (ops.setindex array indices value) state = .ok ((), state') →
    StateT.run (ops.getindex array indices) state' = .ok (value, state')) ∧
  (∀ array indices other newValue oldValue state state',
    indices ≠ other →
    StateT.run (ops.getindex array other) state = .ok (oldValue, state) →
    StateT.run (ops.setindex array indices newValue) state = .ok ((), state') →
    StateT.run (ops.getindex array other) state' = .ok (oldValue, state')) ∧
  ReverseViewLaw ops


/-- `copymutable` preserves contents and mutations of its result do not affect its source. -/
def ReverseCopyLaw {Store A V Axis : Type}
    (ops : ReverseOps (Effect Store) A V Axis)
    (copyMutable : A → Effect Store A) : Prop :=
  ∀ array state copied state',
    StateT.run (copyMutable array) state = .ok (copied, state') →
    (∀ axes, ops.index.axes array = .ok axes → ops.index.axes copied = .ok axes) ∧
    (∀ indices value,
      StateT.run (ops.getindex array indices) state = .ok (value, state) →
      StateT.run (ops.getindex array indices) state' = .ok (value, state') ∧
      StateT.run (ops.getindex copied indices) state' = .ok (value, state')) ∧
    (∀ writeIndices newValue finalState,
      StateT.run (ops.setindex copied writeIndices newValue) state' =
        .ok ((), finalState) →
      ∀ indices value,
        StateT.run (ops.getindex array indices) state = .ok (value, state) →
        StateT.run (ops.getindex array indices) finalState = .ok (value, finalState))

/-- The postcondition for reversing an array handle along `dims`. -/
def ReverseResultValues {Store A V Axis : Type}
    (ops : ReverseOps (Effect Store) A V Axis) (rank : Nat) (dims : List I64)
    (array : A) (state : Store) (outcome : Result (A × Store)) : Prop :=
  ∀ (output : A) (state' : Store) (axes : List Axis) (firsts lasts index : List I64)
    (value : V),
    dims.length ≤ rank →
    dims.length = (dimensions rank).countP (fun dim => dims.contains dim) →
    ops.index.axes array = .ok axes →
    AxisEndpoints ops.index axes firsts lasts →
    firsts.length = rank → lasts.length = rank →
    index ∈ cartesianIndices (axes.map ops.index.indices) →
    outcome = .ok (output, state') →
    stateValue (ops.getindex array
      (reflectedIndex ((dimensions rank).map fun dimension => dims.contains dimension)
        ((firsts.zip lasts).map fun pair => pair.2 + pair.1) index)) state = some value →
    stateValue (ops.getindex output index) state' = some value


/-- The source's tie rule: equal-rank shapes select the right-hand shape. -/
def longerShape {Shape : Type} (length : Shape → I64) (left right : Shape) : Shape :=
  if length left > length right then left else right


/-- `size` length agrees with the array's reported dimension count. -/
def ArraySizeRankLaw {A Shape : Type} (size : A → Result Shape)
    (shapeLength : Shape → I64) (ndims : A → I64) : Prop :=
  ∀ array shape, size array = .ok shape → shapeLength shape = ndims array
/-- Successful reshape preserves the selected shape and every indexed value. -/
def ReshapeShapeValues {A Shape V : Type} (size : A → Result Shape)
    (reshape : A → Shape → Result A) (get : A → I64 → Result V) : Prop :=
  ∀ array shape output index value,
    reshape array shape = .ok output →
    size output = .ok shape ∧
    (get array index = .ok value → get output index = .ok value)

/-- `mapreduce` selects an input shape of maximal rank. -/
def LongestShapeMapreduceLaw {A Shape : Type} (size : A → Result Shape)
    (shapeLength : Shape → I64)
    (mapreduce : (A → Result Shape) → (Shape → Shape → Shape) → List A → Result Shape) : Prop :=
  ∀ arrays shape,
    mapreduce size (longerShape shapeLength) arrays = .ok shape →
    ∃ selected, selected ∈ arrays ∧ size selected = .ok shape ∧
      ∀ array sourceShape, array ∈ arrays → size array = .ok sourceShape →
        shapeLength sourceShape ≤ shapeLength shape

/-- Compatible inputs of the selected rank already have the selected shape. -/
def BroadcastRankInputShapeLaw {A Shape : Type} (size : A → Result Shape)
    (shapeLength : Shape → I64) (ndims : A → I64)
    (mapreduce : (A → Result Shape) → (Shape → Shape → Shape) → List A → Result Shape) : Prop :=
  ∀ arrays shape,
    mapreduce size (longerShape shapeLength) arrays = .ok shape →
    ∀ array, array ∈ arrays → ndims array = shapeLength shape → size array = .ok shape

/-- Mapping equal-shaped arrays preserves their shape. -/
def MappedResultShapeLaw {A Shape F R : Type} (size : A → Result Shape)
    (resultShape : R → Result Shape) (mapArrays : F → List A → Result R) : Prop :=
  ∀ f arrays shape output,
    (∀ array, array ∈ arrays → size array = .ok shape) →
    mapArrays f arrays = .ok output →
    resultShape output = .ok shape


/-- A shape check failure is returned before array mapping. -/
def ShapeChecksOk {A : Type} (promoteShape : A → A → Result Unit)
    (a : A) : List A → Prop
  | [] => True
  | c :: cs => promoteShape a c = .ok () ∧ ShapeChecksOk promoteShape a cs

/-! Nothing to promise: `_broadcast_preserving_zero_d(f,A,B)@5` forwards to Base's
`broadcast_preserving_zero_d` and adds no independent behavior. -/

/-! Nothing to promise: `_reverse!(A::AbstractVector,dim::Tuple{Int})@133` resolves an ambiguity
by forwarding the tuple's sole integer to the integer-dimension method. -/

/-- Equal-rank array `+` and `-` apply their element operator at each shared index. -/
def ArrayBinaryPointwise : Prop :=
  ∀ {A R V F : Type} (mapArrays : F → A → A → List A → Result R)
    (get : A → I64 → Result V) (getResult : R → I64 → Result V)
    (apply : F → V → V → Result V),
    BinaryMapLaw mapArrays get getResult apply →
    ∀ (promoteShape : A → A → Result Unit) (plus minus : F) (a b : A)
      (i : I64) (x y zPlus zMinus : V),
      promoteShape a b = .ok () → get a i = .ok x → get b i = .ok y →
      apply plus x y = .ok zPlus → apply minus x y = .ok zMinus →
        (∃ output, addAbstractArrays promoteShape (broadcastSameRankBinary mapArrays) plus a b =
          .ok output ∧ getResult output i = .ok zPlus) ∧
        (∃ output, subtractAbstractArrays promoteShape (broadcastSameRankBinary mapArrays) minus a b =
          .ok output ∧ getResult output i = .ok zMinus)

def AbstractArrayBinaryPointwise : Prop :=
  ∀ {A B R V F : Type} (broadcast : F → A → B → Result R)
    (getA : A → I64 → Result V) (getB : B → I64 → Result V)
    (getResult : R → I64 → Result V) (apply : F → V → V → Result V),
    BinaryBroadcastLaw (broadcastDefault broadcast) getA getB getResult apply →
    ∀ (promoteShape : A → B → Result Unit) (plus minus : F) (a : A) (b : B)
      (i : I64) (x y zPlus zMinus : V),
      promoteShape a b = .ok () → getA a i = .ok x → getB b i = .ok y →
      apply plus x y = .ok zPlus → apply minus x y = .ok zMinus →
        (∃ output, addAbstractArrays promoteShape (broadcastDefault broadcast) plus a b =
          .ok output ∧ getResult output i = .ok zPlus) ∧
        (∃ output, subtractAbstractArrays promoteShape (broadcastDefault broadcast) minus a b =
          .ok output ∧ getResult output i = .ok zMinus)

def ArrayVariadicPointwise : Prop :=
  ∀ {A R V F : Type} (mapArrays : F → A → A → List A → Result R)
    (get : A → I64 → Result V) (getResult : R → I64 → Result V)
    (apply : F → V → V → List V → Result V),
    VariadicMapLaw mapArrays get getResult apply →
    ∀ (promoteShape : A → A → Result Unit) (plus : F) (a b : A)
      (cs : List A) (i : I64) (x y z : V) (xs : List V),
      promoteShape a b = .ok () → ShapeChecksOk promoteShape a cs →
      get a i = .ok x → get b i = .ok y → valuesAt get i cs = .ok xs →
      apply plus x y xs = .ok z →
      ∃ output, addArrayMany promoteShape (broadcastSameRank mapArrays) plus a b cs = .ok output ∧
        getResult output i = .ok z

def MixedRankBinaryPointwise : Prop :=
  ∀ {A B R V F : Type} (ndimsA : A → I64) (ndimsB : B → I64)
    (broadcast : F → A → B → Result R)
    (getA : A → I64 → Result V) (getB : B → I64 → Result V)
    (getResult : R → I64 → Result V) (apply : F → V → V → Result V),
    BinaryBroadcastLaw (broadcastDefault broadcast) getA getB getResult apply →
    ∀ (promoteShape : A → B → Result Unit) (plus minus : F) (a : A) (b : B)
      (i : I64) (x y zPlus zMinus : V),
      ndimsA a ≠ ndimsB b →
      promoteShape a b = .ok () → getA a i = .ok x → getB b i = .ok y →
      apply plus x y = .ok zPlus → apply minus x y = .ok zMinus →
        (∃ output, addAbstractArrays promoteShape (broadcastDefault broadcast) plus a b =
          .ok output ∧ getResult output i = .ok zPlus) ∧
        (∃ output, subtractAbstractArrays promoteShape (broadcastDefault broadcast) minus a b =
          .ok output ∧ getResult output i = .ok zMinus)

def MixedRankVariadicPointwise : Prop :=
  ∀ {A Shape R V F : Type} (size : A → Result Shape) (shapeLength : Shape → I64)
    (mapreduce : (A → Result Shape) → (Shape → Shape → Shape) → List A → Result Shape)
    (ndims : A → I64) (reshape : A → Shape → Result A)
    (mapArrays : F → List A → Result R) (get : A → I64 → Result V)
    (getResult : R → I64 → Result V) (shapeResult : R → Result Shape)
    (apply : F → List V → Result V),
    ManyArrayMapLaw mapArrays get getResult apply →
    ReshapeShapeValues size reshape get →
    ArraySizeRankLaw size shapeLength ndims →
    LongestShapeMapreduceLaw size shapeLength mapreduce →
    BroadcastRankInputShapeLaw size shapeLength ndims mapreduce →
    MappedResultShapeLaw size shapeResult mapArrays →
    ∀ (promoteShape : A → A → Result Unit) (plus : F) (a b : A) (cs : List A)
      (i : I64) (values : List V) (result : V) (shape : Shape),
      promoteShape a b = .ok () → ShapeChecksOk promoteShape a cs →
      mapreduce size (longerShape shapeLength) (a :: b :: cs) = .ok shape →
      valuesAt get i (a :: b :: cs) = .ok values →
      apply plus values = .ok result →
      ∃ output, addArrayMany promoteShape
        (broadcastArrayRanks size shapeLength mapreduce ndims reshape mapArrays)
        plus a b cs = .ok output ∧ shapeResult output = .ok shape ∧
        getResult output i = .ok result

def MixedRankArrayArithmeticPointwise : Prop :=
  MixedRankBinaryPointwise ∧ MixedRankVariadicPointwise

def ArrayArithmeticPointwise : Prop :=
  ∀ {A R V : Type} (map : (V → Result V) → A → Result R)
    (get : A → I64 → Result V) (getResult : R → I64 → Result V)
    (plus : V → Result V)
    (fix1 fix2 : (V → V → Result V) → V → (V → Result V))
    (apply : V → V → Result V),
    UnaryMapLaw map get getResult →
    (∀ x, plus x = .ok x) →
    (∀ f scalar x y, f scalar x = .ok y → fix1 f scalar x = .ok y) →
    (∀ f scalar x y, f x scalar = .ok y → fix2 f scalar x = .ok y) →
    ∀ (a : A) (scalar : V) (f : V → V → Result V) (i : I64) (x y : V),
      (get a i = .ok x →
        (∃ output, unaryArrayPlus map plus a = .ok output ∧ getResult output i = .ok x)) ∧
      (get a i = .ok x → apply scalar x = .ok y →
        (∃ output, ldivScalarArray (broadcastScalarArray fix1 map) f scalar a =
          .ok output ∧ getResult output i = .ok y) ∧
        (∃ output, mulScalarArray (broadcastScalarArray fix1 map) f scalar a =
          .ok output ∧ getResult output i = .ok y)) ∧
      (get a i = .ok x → apply x scalar = .ok y →
        (∃ output, divArrayScalar (broadcastArrayScalar fix2 map) f a scalar =
          .ok output ∧ getResult output i = .ok y) ∧
        (∃ output, mulArrayScalar (broadcastArrayScalar fix2 map) f a scalar =
          .ok output ∧ getResult output i = .ok y))

/-- Incompatible shapes raise the first `promote_shape` error before mapping. -/
def ArrayShapeErrors : Prop :=
  ∀ {A F R : Type} (mapArrays : F → A → A → List A → Result R)
    (promoteShape : A → A → Result Unit) (f : F) (a b : A) (cs : List A)
    (e : JuliaLean.base.abstractarray.ArrayError),
    (promoteShape a b = .error e →
      addArrayMany promoteShape (broadcastSameRank mapArrays) f a b cs = .error e) ∧
    (∀ prior c suffix,
      promoteShape a b = .ok () → ShapeChecksOk promoteShape a prior →
      promoteShape a c = .error e →
      addArrayMany promoteShape (broadcastSameRank mapArrays) f a b
        (prior ++ c :: suffix) = .error e)
def AbstractArrayShapeErrors : Prop :=
  ∀ {A B F R : Type} (broadcast : F → A → B → Result R)
    (promoteShape : A → B → Result Unit) (f : F) (a : A) (b : B)
    (e : JuliaLean.base.abstractarray.ArrayError),
    promoteShape a b = .error e →
    addAbstractArrays promoteShape (broadcastDefault broadcast) f a b = .error e ∧
    subtractAbstractArrays promoteShape (broadcastDefault broadcast) f a b = .error e

/-- The rank helper selects a maximal-rank shape, preserves input values, and maps that shape. -/
def BroadcastRankShapeAndValues : Prop :=
  ∀ {A Shape F R V : Type} (size : A → Result Shape) (shapeLength : Shape → I64)
    (mapreduce : (A → Result Shape) → (Shape → Shape → Shape) → List A → Result Shape)
    (ndims : A → I64) (reshape : A → Shape → Result A)
    (mapArrays : F → List A → Result R) (get : A → I64 → Result V)
    (getResult : R → I64 → Result V) (shapeResult : R → Result Shape)
    (apply : F → List V → Result V),
    ManyArrayMapLaw mapArrays get getResult apply →
    ReshapeShapeValues size reshape get →
    LongestShapeMapreduceLaw size shapeLength mapreduce →
    BroadcastRankInputShapeLaw size shapeLength ndims mapreduce →
    MappedResultShapeLaw size shapeResult mapArrays →
    ∀ f a b cs i values result output shape,
      valuesAt get i (a :: b :: cs) = .ok values →
      mapreduce size (longerShape shapeLength) (a :: b :: cs) = .ok shape →
      apply f values = .ok result →
      broadcastArrayRanks size shapeLength mapreduce ndims reshape mapArrays f a b cs =
        .ok output →
      shapeResult output = .ok shape ∧ getResult output i = .ok result

def ReverseInvalidDimensions : Prop :=
  ∀ {Store A V Axis : Type} (ops : ReverseOps (Effect Store) A V Axis)
    (rank : Nat) (array : A) (dims : List I64) (state : Store),
    (∀ {α : Type} (error : JuliaLean.base.abstractarray.ArrayError) (s : Store),
      StateT.run (ops.raise (α := α) error) s = .error error) →
    dims ≠ [] →
    (rank < dims.length ∨
      dims.length ≠ (dimensions rank).countP (fun dim => dims.contains dim)) →
    StateT.run (reverseBang (reverseBangCore ops rank) array dims) state =
      .error (.julia (.argumentError
        ("invalid dimensions " ++ ops.showDims dims ++ " in reverse!")))

def ReversePreservesInput : Prop :=
  ∀ {Store A V Axis : Type} (ops : ReverseOps (Effect Store) A V Axis)
    (rank : Nat) (copyMutable : A → Effect Store A) (array : A) (dims : List I64)
    (state : Store),
    ReverseOpsLaws ops →
    ReverseCopyLaw ops copyMutable →
    ReverseResultValues ops rank dims array state
      (StateT.run
        (reverse (reverseCopy copyMutable (reverseBang (reverseBangCore ops rank))) array dims)
        state) ∧
    (∀ (output : A) (state' : Store) (index : List I64) (value : V),
      StateT.run
        (reverse (reverseCopy copyMutable (reverseBang (reverseBangCore ops rank))) array dims)
        state = .ok (output, state') →
      stateValue (ops.getindex array index) state = some value →
      stateValue (ops.getindex array index) state' = some value)
def ReverseCoordinateContract : Prop :=
  ∀ {Store A V Axis : Type} (ops : ReverseOps (Effect Store) A V Axis)
    (rank : Nat) (dims : List I64) (array : A) (state : Store),
    ReverseOpsLaws ops →
    ReverseResultValues ops rank dims array state
      (StateT.run (reverseBang (reverseBangCore ops rank) array dims) state) ∧
    ReverseResultValues ops rank (dimensions rank) array state
      (StateT.run (reverseBangColon (reverseBangCore ops rank) rank array) state)

/-- Successful integer conversions reach reversal and preserve reflected values. -/
def ReverseDimensionConversionSuccess : Prop :=
  ∀ {Store A V Axis D : Type} (ops : ReverseOps (Effect Store) A V Axis)
    (rank : Nat) (array : A) (toInt : D → Effect Store I64)
    (dim : D) (dims : List D) (state : Store),
    ReverseOpsLaws ops →
    (∀ converted conversionState output state',
      StateT.run (toInt dim) state = .ok (converted, conversionState) →
      StateT.run (reverseBangInteger (reverseBangCore ops rank) toInt array dim) state =
        .ok (output, state') →
      ReverseResultValues ops rank [converted] array conversionState (.ok (output, state'))) ∧
    (∀ converted conversionState output state',
      StateT.run (dims.mapM toInt) state = .ok (converted, conversionState) →
      StateT.run (reverseBangIntegerTuple (reverseBangCore ops rank) toInt array dims) state =
        .ok (output, state') →
      ReverseResultValues ops rank converted array conversionState (.ok (output, state')))


def FirstConversionError {Store D : Type} (toInt : D → Effect Store I64) :
    List D → Store → JuliaLean.base.abstractarray.ArrayError → Prop
  | [], _, _ => False
  | dimension :: dimensions, state, error =>
      StateT.run (toInt dimension) state = .error error ∨
      ∃ value state', StateT.run (toInt dimension) state = .ok (value, state') ∧
        FirstConversionError toInt dimensions state' error

/-- Integer-to-Int conversion errors are returned before reversal starts. -/
def ReverseDimensionConversionErrors : Prop :=
  ∀ {Store A V Axis D : Type} (ops : ReverseOps (Effect Store) A V Axis)
    (rank : Nat) (array : A) (toInt : D → Effect Store I64)
    (dim : D) (dims : List D) (state : Store) (e : JuliaLean.base.abstractarray.ArrayError),
    (StateT.run (toInt dim) state = .error e →
      StateT.run (reverseBangInteger (reverseBangCore ops rank) toInt array dim) state = .error e) ∧
    (FirstConversionError toInt dims state e →
      StateT.run (reverseBangIntegerTuple (reverseBangCore ops rank) toInt array dims) state = .error e)

/-- For every Cartesian source coordinate, `reverseBangCore`'s reflected access stays in the axes. -/
def ReverseInBounds : Prop :=
  ∀ {Store A V Axis : Type} (ops : ReverseOps (Effect Store) A V Axis)
    (rank : Nat) (dims : List I64) (array : A) (state : Store)
    (output : A) (state' : Store) (axes : List Axis) (firsts lasts index : List I64),
    ReverseOpsLaws ops →
    dims.length ≤ rank →
    dims.length = (dimensions rank).countP (fun dim => dims.contains dim) →
    ops.index.axes array = .ok axes →
    AxisEndpoints ops.index axes firsts lasts →
    firsts.length = rank → lasts.length = rank →
    StateT.run (reverseBangCore ops rank array dims) state = .ok (output, state') →
    index ∈ cartesianIndices (axes.map ops.index.indices) →
    index ∈ cartesianIndices (axes.map ops.index.indices) ∧
      reflectedIndex
        ((dimensions rank).map fun dimension => dims.contains dimension)
        ((firsts.zip lasts).map fun pair => pair.2 + pair.1) index ∈
          cartesianIndices (axes.map ops.index.indices)

/-- The direct matrix rotations place each source element at the documented coordinate. -/
def MatrixRotationLaw {Store A B V Axis : Type}
    (ops : MatrixOps (Effect Store) A B V Axis)
    (getOutput : B → I64 → I64 → Effect Store V)
    (rotate : A → Effect Store B)
    (target : I64 → I64 → I64 → I64 → I64 → I64 → I64 × I64) : Prop :=
  ∀ (array : A) (state : Store) (output : B) (state' : Store)
    (axis1 axis2 : Axis) (first1 last1 first2 last2 i j : I64) (value : V),
    ops.index.axes array = .ok [axis1, axis2] →
    ops.index.first axis1 = .ok first1 → ops.index.last axis1 = .ok last1 →
    ops.index.first axis2 = .ok first2 → ops.index.last axis2 = .ok last2 →
    i ∈ ops.values axis1 → j ∈ ops.values axis2 →
    StateT.run (rotate array) state = .ok (output, state') →
    stateValue (ops.getindex array i j) state = some value →
    stateValue (getOutput output (target first1 last1 first2 last2 i j).1
      (target first1 last1 first2 last2 i j).2) state' = some value

/-- Matrix axes, allocations, and stateful indexing obey the AbstractArray contract. -/
def MatrixOpsLaws {Store A B V Axis : Type}
    (ops : MatrixOps (Effect Store) A B V Axis)
    (outputAxes : B → Result (List Axis))
    (getOutput : B → I64 → I64 → Effect Store V) : Prop :=
  AxisIndexRangeLaw ops.index ∧
  (∀ axis, ops.values axis = ops.index.indices axis) ∧
  (∀ array i j value state state',
    StateT.run (ops.getindex array i j) state = .ok (value, state') →
    state' = state) ∧
  (∀ output i j value state state',
    StateT.run (getOutput output i j) state = .ok (value, state') →
    state' = state) ∧
  (∀ output i j value state state',
    StateT.run (ops.setindex output i j value) state = .ok ((), state') →
    StateT.run (getOutput output i j) state' = .ok (value, state')) ∧
  (∀ output i j i' j' newValue oldValue state state',
    (i, j) ≠ (i', j') →
    StateT.run (getOutput output i' j') state = .ok (oldValue, state) →
    StateT.run (ops.setindex output i j newValue) state = .ok ((), state') →
    StateT.run (getOutput output i' j') state' = .ok (oldValue, state')) ∧
  (∀ array axis1 axis2 output state state',
    StateT.run (ops.similar array axis2 axis1) state = .ok (output, state') →
    outputAxes output = .ok [axis2, axis1]) ∧
  (∀ array axes output state state',
    ops.index.axes array = .ok axes →
    StateT.run (ops.similarSame array) state = .ok (output, state') →
    outputAxes output = .ok axes)

/-- Matrix copies preserve axes and values, and writes to a copy leave its source unchanged. -/
def MatrixCopyLaw {Store A B V Axis : Type}
    (ops : MatrixOps (Effect Store) A B V Axis)
    (outputAxes : B → Result (List Axis))
    (getOutput : B → I64 → I64 → Effect Store V)
    (copy : A → Effect Store B) : Prop :=
  ∀ array state copied state',
    StateT.run (copy array) state = .ok (copied, state') →
    (∀ axes, ops.index.axes array = .ok axes → outputAxes copied = .ok axes) ∧
    (∀ i j value,
      StateT.run (ops.getindex array i j) state = .ok (value, state) →
      StateT.run (ops.getindex array i j) state' = .ok (value, state') ∧
      StateT.run (getOutput copied i j) state' = .ok (value, state')) ∧
    (∀ writeI writeJ newValue finalState,
      StateT.run (ops.setindex copied writeI writeJ newValue) state' =
        .ok ((), finalState) →
      ∀ i j value,
        StateT.run (ops.getindex array i j) state = .ok (value, state) →
        StateT.run (ops.getindex array i j) finalState = .ok (value, finalState))

def leftTarget (_first1 _last1 first2 last2 i j : I64) : I64 × I64 :=
  (first2 + last2 - j, i)

def rightTarget (first1 last1 _first2 _last2 i j : I64) : I64 × I64 :=
  (j, first1 + last1 - i)

def halfTarget (first1 last1 first2 last2 i j : I64) : I64 × I64 :=
  (first1 + last1 - i, first2 + last2 - j)

def MatrixRotationCoordinates : Prop :=
  ∀ {Store A B V Axis : Type} (ops : MatrixOps (Effect Store) A B V Axis)
    (outputAxes : B → Result (List Axis))
    (getOutput : B → I64 → I64 → Effect Store V),
    MatrixOpsLaws ops outputAxes getOutput →
    MatrixRotationLaw ops getOutput (rotateLeftMatrix ops) leftTarget ∧
    MatrixRotationLaw ops getOutput (rotateRightMatrix ops) rightTarget ∧
    MatrixRotationLaw ops getOutput (rotateHalfMatrix ops) halfTarget

def CountedMatrixRotationLaw {Store A B V Axis K : Type}
    (ops : MatrixOps (Effect Store) A B V Axis)
    (getOutput : B → I64 → I64 → Effect Store V)
    (rotate : A → K → Effect Store B)
    (target : K → I64 → I64 → I64 → I64 → I64 → I64 → I64 × I64) : Prop :=
  ∀ (array : A) (count : K) (state : Store) (output : B) (state' : Store)
    (axis1 axis2 : Axis) (first1 last1 first2 last2 i j : I64) (value : V),
    ops.index.axes array = .ok [axis1, axis2] →
    ops.index.first axis1 = .ok first1 → ops.index.last axis1 = .ok last1 →
    ops.index.first axis2 = .ok first2 → ops.index.last axis2 = .ok last2 →
    i ∈ ops.values axis1 → j ∈ ops.values axis2 →
    StateT.run (rotate array count) state = .ok (output, state') →
    stateValue (ops.getindex array i j) state = some value →
    stateValue (getOutput output (target count first1 last1 first2 last2 i j).1
      (target count first1 last1 first2 last2 i j).2) state' = some value

def quarterTargetFor {K : Type} (residue : K → Nat) (count : K)
    (first1 last1 first2 last2 i j : I64) : I64 × I64 :=
  match residue count % 4 with
  | 0 => (i, j)
  | 1 => (first2 + last2 - j, i)
  | 2 => (first1 + last1 - i, first2 + last2 - j)
  | _ => (j, first1 + last1 - i)

def halfTargetFor {K : Type} (residue : K → Nat) (count : K)
    (first1 last1 first2 last2 i j : I64) : I64 × I64 :=
  if decide (residue count % 2 = 1) then
    (first1 + last1 - i, first2 + last2 - j) else (i, j)
def quarterTarget (turn : Nat) (first1 last1 first2 last2 i j : I64) : I64 × I64 :=
  match turn % 4 with
  | 0 => (i, j)
  | 1 => (first2 + last2 - j, i)
  | 2 => (first1 + last1 - i, first2 + last2 - j)
  | _ => (j, first1 + last1 - i)

def halfCountTarget (odd : Bool) (first1 last1 first2 last2 i j : I64) : I64 × I64 :=
  if odd then (first1 + last1 - i, first2 + last2 - j) else (i, j)
/- Counted rotations agree with the coordinate transform for their mathematical turn count. -/
def CountedRotationCoordinates : Prop :=
  ∀ {Store A B V Axis K : Type} (ops : MatrixOps (Effect Store) A B V Axis)
    (outputAxes : B → Result (List Axis))
    (getOutput : B → I64 → I64 → Effect Store V)
    (mod : K → I64 → Effect Store K) (equals : K → I64 → Effect Store Bool)
    (negate : K → Effect Store K) (copy : A → Effect Store B)
    (residue negativeResidue : K → Nat),
    MatrixOpsLaws ops outputAxes getOutput →
    MatrixCopyLaw ops outputAxes getOutput copy →
    MatrixRotationLaw ops getOutput (rotateLeftMatrix ops) (quarterTarget 1) →
    MatrixRotationLaw ops getOutput (rotateHalfMatrix ops) (quarterTarget 2) →
    MatrixRotationLaw ops getOutput (rotateRightMatrix ops) (quarterTarget 3) →
    (∀ count state reduced,
      StateT.run (mod count (JuliaLean.base.abstractarray.int 4)) state = .ok (reduced, state) →
      residue reduced = residue count % 4) →
    (∀ count state reduced,
      StateT.run (mod count (JuliaLean.base.abstractarray.int 2)) state = .ok (reduced, state) →
      residue reduced = residue count % 2) →
    (∀ count state opposite,
      StateT.run (negate count) state = .ok (opposite, state) →
      residue opposite = negativeResidue count % 4) →
    (∀ value n state, n < 4 →
      StateT.run (equals value (JuliaLean.base.abstractarray.int (Int.ofNat n))) state =
        .ok (decide (residue value = n), state)) →
    CountedMatrixRotationLaw ops getOutput
      (rotateLeftCounted (m := Effect Store) (A := A) (K := K) (B := B)
        mod equals (rotateLeftMatrix ops) (rotateHalfMatrix ops) (rotateRightMatrix ops) copy)
      (quarterTargetFor residue) ∧
    CountedMatrixRotationLaw ops getOutput
      (rotateRightCounted (m := Effect Store) (A := A) (K := K) (B := B)
        negate mod equals (rotateLeftMatrix ops) (rotateHalfMatrix ops) (rotateRightMatrix ops) copy)
      (quarterTargetFor negativeResidue) ∧
    CountedMatrixRotationLaw ops getOutput
      (rotateHalfCounted (m := Effect Store) (A := A) (K := K) (B := B)
        mod equals (rotateHalfMatrix ops) copy)
      (halfTargetFor residue)

private def entry (id : String) (juliaFns : List String) (statement source : String)
    (prop : Lean.Name) : Entry :=
  { id, juliaFile := "base/arraymath.jl", juliaFns, statement, source,
    status := .todo, prop }


namespace Round3

open JuliaLean JuliaLean.base.arraymath JuliaLean.Proofs.base.arraymath

abbrev PrecheckEffect (Store : Type) :=
  StateT Store JuliaLean.base.abstractarray.Result

/-- A tuple names distinct existing dimensions; this is independent of the
implementation's Boolean membership count. -/
def ValidDimensionSet (rank : Nat)
    (dims : List JuliaLean.base.arraymath.I64) : Prop :=
  dims.Nodup ∧ ∀ d ∈ dims, 1 ≤ d.val ∧ d.val ≤ (rank : Int)

/-- Bind throwing to the language exception operation. Array operations are
universally quantified and have no correctness assumptions; invalid dimensions
must be rejected before those operations run. Pure native-tuple presentation is
also unrestricted, since the contract does not specify the message. -/
def precheckOps {Store A V Axis : Type}
    (ops : ReverseOps (PrecheckEffect Store) A V Axis) :
    ReverseOps (PrecheckEffect Store) A V Axis :=
  { ops with raise := fun error => fun _ => .error error }

/- The singleton-vector tuple overload is a separate forwarding method, so
its dispatch case is excluded below. The adapter selects the public wrapper
without reimplementing reversal. -/
def genericTupleReverse {Store A V Axis : Type}
    (ops : ReverseOps (PrecheckEffect Store) A V Axis)
    (rank : Nat) (a : A) (dims : List JuliaLean.base.arraymath.I64) :
    PrecheckEffect Store A :=
  if rank = 1 then
    JuliaLean.base.array.reverseDims
      (JuliaLean.base.arraymath.reverseBangCore (precheckOps ops) rank) a dims
  else
    JuliaLean.base.arraymath.reverseBang
      (JuliaLean.base.arraymath.reverseBangCore (precheckOps ops) rank) a dims

/-- The public in-place reversal rejects every repeated or nonexistent native
dimension tuple on the generic tuple method's complete dispatch domain.
Julia source: base/arraymath.jl:103,107-131; base/array.jl:2264-2272 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Julia documentation: base/arraymath.jl:63-68,95-101; doc/src/manual/arrays.md:38-43; the invalid-dimension invariant enforced at base/arraymath.jl:108-113 @ f755f49a9e41380d7da126b3c1db9fe7f83dd027
Rank and tuple arity range over every nonnegative representable native Int.
The precheck only converts k+1 with k+1 ≤ rank; its membership count and length
comparisons stay in Nat. No doubled length or offset arithmetic is reached.
-/
def ReverseInvalidDimensionsCorrect : Prop :=
  ∀ {Store A V Axis : Type}
    (ops : ReverseOps (PrecheckEffect Store) A V Axis)
    (rank : Nat) (a : A) (dims : List JuliaLean.base.arraymath.I64)
    (state : Store),
    rank < 2 ^ 63 → dims.length < 2 ^ 63 →
    (rank ≠ 1 ∨ dims.length ≠ 1) →
    ¬ ValidDimensionSet rank dims →
    ∃ message : String,
      StateT.run (genericTupleReverse ops rank a dims) state =
        .error (.julia (.argumentError message))

end Round3

end JuliaLean.Proofs.base.arraymath

namespace JuliaLean.ChatGPT.Batch4.Group22
open JuliaLean.Proofs.base.arraymath
open JuliaLean.base.arraymath hiding I64 Result

theorem arraymath_shape_loop_first_error {A : Type}
    (promoteShape : A → A → Result Unit) (a : A) (prior : List A)
    (c : A) (suffix : List A) (e : JuliaLean.base.abstractarray.ArrayError)
    (checks : ShapeChecksOk promoteShape a prior) (failure : promoteShape a c = .error e) :
    (forIn (prior ++ c :: suffix) PUnit.unit fun d _ => do
      promoteShape a d
      pure (ForInStep.yield PUnit.unit) : Result PUnit) = .error e := by
  induction prior with
  | nil => simp only [List.nil_append, List.forIn_cons, failure, bind, Except.bind]
  | cons p ps ih =>
      rcases checks with ⟨hp, hps⟩
      simp only [List.cons_append, List.forIn_cons, hp, bind, Except.bind, pure, Except.pure]
      exact ih hps

theorem ArraymathShapeErrors_proven : JuliaLean.Proofs.base.arraymath.ArrayShapeErrors := by
  intro A F R mapArrays promoteShape f a b cs e
  constructor
  · intro h
    simp only [addArrayMany, h, bind, Except.bind]
  · intro prior c suffix hab hprior hc
    unfold addArrayMany
    rw [hab]
    dsimp only [bind, Except.bind]
    have hloop := arraymath_shape_loop_first_error promoteShape a prior c suffix e hprior hc
    dsimp only [bind, Except.bind] at hloop
    rw [hloop]

theorem ArraymathAbstractarrayShapeErrors_proven : JuliaLean.Proofs.base.arraymath.AbstractArrayShapeErrors := by
  intro A B F R broadcast promoteShape f a b e h
  constructor <;> simp only [addAbstractArrays, subtractAbstractArrays, h, bind, Except.bind]

theorem arraymath_run_bind {Store A B : Type} (action : Effect Store A)
    (next : A → Effect Store B) (state : Store) :
    StateT.run (action >>= next) state =
      match StateT.run action state with
      | .error e => .error e
      | .ok (value, nextState) => StateT.run (next value) nextState := by
  cases h : action state with
  | error e => simp only [StateT.run, bind, StateT.bind, Except.bind, h]
  | ok pair =>
      cases pair
      simp only [StateT.run, bind, StateT.bind, Except.bind, h]

theorem arraymath_first_conversion_error {Store D : Type}
    (toInt : D → Effect Store I64) (dims : List D) (state : Store)
    (e : JuliaLean.base.abstractarray.ArrayError)
    (failure : FirstConversionError toInt dims state e) :
    StateT.run (dims.mapM toInt) state = .error e := by
  induction dims generalizing state with
  | nil => exact False.elim failure
  | cons d ds ih =>
      rcases failure with hd | ⟨value, next, hd, hds⟩
      · simp only [List.mapM_cons, arraymath_run_bind, hd]
      · simp only [List.mapM_cons, arraymath_run_bind, hd, ih next hds]

theorem ArraymathReverseDimensionConversion_proven : JuliaLean.Proofs.base.arraymath.ReverseDimensionConversionErrors := by
  intro Store A V Axis D ops rank array toInt dim dims state e
  constructor
  · intro h
    simp only [reverseBangInteger, arraymath_run_bind, h]
  · intro h
    simp only [reverseBangIntegerTuple, arraymath_run_bind,
      arraymath_first_conversion_error toInt dims state e h]

theorem arraymath_bind_ok {A B : Type} (action : Result A)
    (next : A → Result B) (output : B)
    (success : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases ha : action with
  | error e =>
      simp only [ha, bind, Except.bind] at success
      cases success
  | ok value =>
      exact ⟨value, rfl, by simpa only [ha, bind, Except.bind] using success⟩

theorem arraymath_mapM_preserves_values {A Shape V : Type}
    (transform : A → Result A) (size : A → Result Shape)
    (get : A → I64 → Result V) (shape : Shape) (i : I64)
    (arrays mapped : List A) (values : List V)
    (law : ∀ array ∈ arrays, ∀ output, transform array = .ok output →
      size output = .ok shape ∧
      ∀ value, get array i = .ok value → get output i = .ok value)
    (hmap : arrays.mapM transform = .ok mapped)
    (hvalues : valuesAt get i arrays = .ok values) :
    (∀ array ∈ mapped, size array = .ok shape) ∧ valuesAt get i mapped = .ok values := by
  induction arrays generalizing mapped values with
  | nil =>
      have he : mapped = [] := by
        have h : Except.ok ([] : List A) = Except.ok mapped := hmap
        exact (Except.ok.inj h).symm
      subst mapped
      constructor
      · intro array h
        cases h
      · exact hvalues
  | cons a as ih =>
      rw [List.mapM_cons] at hmap
      obtain ⟨a', ha', hrest⟩ := arraymath_bind_ok _ _ _ hmap
      obtain ⟨as', has', hend⟩ := arraymath_bind_ok _ _ _ hrest
      have hmapped : a' :: as' = mapped := Except.ok.inj hend
      subst mapped
      change (get a i >>= fun value => valuesAt get i as >>= fun rest =>
        pure (value :: rest)) = .ok values at hvalues
      obtain ⟨x, hx, hrestval⟩ := arraymath_bind_ok _ _ _ hvalues
      obtain ⟨xs, hxs, hendval⟩ := arraymath_bind_ok _ _ _ hrestval
      have hvals : x :: xs = values := Except.ok.inj hendval
      subst values
      have head := law a (List.mem_cons_self) a' ha'
      have tail := ih as' xs
        (by intro array hmem; exact law array (List.mem_cons_of_mem a hmem)) has' hxs
      constructor
      · intro array hmem
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact head.1
        · exact tail.1 array hmem
      · simp only [valuesAt, head.2 x hx, tail.2, bind, Except.bind, pure, Except.pure]

theorem ArraymathBroadcastRank_proven : JuliaLean.Proofs.base.arraymath.BroadcastRankShapeAndValues := by
  intro A Shape F R V size shapeLength mapreduce ndims reshape mapArrays get getResult
    shapeResult apply mapLaw reshapeLaw longestLaw inputLaw shapeLaw
    f a b cs i values result output shape hvalues hshape happly hsuccess
  unfold broadcastArrayRanks at hsuccess
  change (mapreduce size (longerShape shapeLength) (a :: b :: cs) >>= _) = .ok output at hsuccess
  rw [hshape] at hsuccess
  change ((a :: b :: cs).mapM (fun array =>
      if shapeLength shape = ndims array then pure array else reshape array shape) >>=
        mapArrays f) = .ok output at hsuccess
  obtain ⟨mapped, hmapped, houtput⟩ := arraymath_bind_ok _ _ _ hsuccess
  have transformed := arraymath_mapM_preserves_values
    (fun array => if shapeLength shape = ndims array then pure array else reshape array shape)
    size get shape i (a :: b :: cs) mapped values
    (by
      intro array hmem newArray hnew
      by_cases heq : shapeLength shape = ndims array
      · simp only [heq, ite_true, pure, Except.pure, Except.ok.injEq] at hnew
        subst newArray
        exact ⟨inputLaw (a :: b :: cs) shape hshape array hmem heq.symm,
          by intro value hvalue; exact hvalue⟩
      · simp only [heq, ite_false] at hnew
        constructor
        · exact (reshapeLaw array shape newArray i result hnew).1
        · intro value hvalue
          exact (reshapeLaw array shape newArray i value hnew).2 hvalue)
    hmapped hvalues
  exact ⟨shapeLaw f mapped shape output transformed.1 houtput,
    mapLaw f mapped output i values result houtput transformed.2 happly⟩


end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.ChatGPT.Batch4.Group22
open JuliaLean JuliaLean.base.arraymath JuliaLean.Proofs.base.arraymath

 theorem amIntWrapValue (z : Int) (hz : IntTy.min .i64 ≤ z ∧ z ≤ IntTy.max .i64) :
    (JInt.wrap .i64 z).val = z := wrapInt_of_inRange .i64 z hz

 theorem amIntRangeMembership (lo hi i : JuliaLean.base.arraymath.I64) :
    i ∈ JuliaLean.base.array.intRange lo hi ↔ lo.val ≤ i.val ∧ i.val ≤ hi.val := by
  constructor
  · intro h
    simp only [JuliaLean.base.array.intRange, List.mem_map, List.mem_range] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hlo := lo.property
    have hhi := hi.property
    rw [amIntWrapValue _ (by omega)]
    omega
  · intro h
    refine List.mem_map.mpr ⟨(i.val - lo.val).toNat, List.mem_range.mpr (by omega), ?_⟩
    apply Subtype.ext
    rw [amIntWrapValue _ (by have := i.property; omega)]
    omega

 theorem amReflectedValue (lo hi i : JuliaLean.base.arraymath.I64)
    (hlo : lo.val ≤ i.val) (hhi : i.val ≤ hi.val) :
    ((hi + lo) - i).val = hi.val + lo.val - i.val := by
  have hl := lo.property
  have hh := hi.property
  change wrapInt .i64 (wrapInt .i64 (hi.val + lo.val) - i.val) = _
  simp only [wrapInt, IntTy.signed, IntTy.bits, IntTy.min, IntTy.max,
    ite_true] at hl hh ⊢
  omega

 theorem amReflectedRange (lo hi i : JuliaLean.base.arraymath.I64)
    (hiMem : i ∈ JuliaLean.base.array.intRange lo hi) :
    (hi + lo) - i ∈ JuliaLean.base.array.intRange lo hi := by
  have hb := (amIntRangeMembership lo hi i).mp hiMem
  apply (amIntRangeMembership lo hi _).mpr
  rw [amReflectedValue lo hi i hb.1 hb.2]
  omega

 theorem amReflectedCartesian {m : Type → Type} {A Axis : Type}
    (ops : ArrayIndexOps m A Axis) (hRange : AxisIndexRangeLaw ops)
    (axes : List Axis) (firsts lasts : List JuliaLean.base.arraymath.I64)
    (flags : List Bool) (index : List JuliaLean.base.arraymath.I64)
    (hEnds : AxisEndpoints ops axes firsts lasts)
    (hFlags : flags.length = axes.length)
    (hIndex : index ∈ cartesianIndices (axes.map ops.indices)) :
    reflectedIndex flags ((firsts.zip lasts).map fun pair => pair.2 + pair.1) index ∈
      cartesianIndices (axes.map ops.indices) := by
  induction axes generalizing firsts lasts flags index with
  | nil =>
    have hf : firsts = [] := List.eq_nil_of_length_eq_zero hEnds.1.symm
    subst firsts
    simp only [List.zip_nil_left, List.map_nil, reflectedIndex, List.zip_nil_right,
      cartesianIndices, List.mem_singleton]
  | cons axis axes ih =>
    cases firsts with
    | nil => simp only [AxisEndpoints, List.length_cons, List.length_nil] at hEnds; omega
    | cons first firsts =>
      cases lasts with
      | nil => simp only [AxisEndpoints, List.length_cons, List.length_nil] at hEnds; omega
      | cons last lasts =>
        cases flags with
        | nil => simp only [List.length_cons, List.length_nil] at hFlags; omega
        | cons flag flags =>
          have hHead := hEnds.2.2 0 (by simp only [List.length_cons]; omega)
          change ops.first axis = .ok first ∧ ops.last axis = .ok last at hHead
          have hTail : AxisEndpoints ops axes firsts lasts := by
            refine ⟨?_, ?_, ?_⟩
            · have h := hEnds.1
              simp only [List.length_cons] at h
              omega
            · have h := hEnds.2.1
              simp only [List.length_cons] at h
              omega
            · intro k hk
              have h := hEnds.2.2 (k + 1) (by simp only [List.length_cons]; omega)
              simpa only [List.getElem?_cons_succ] using h
          have hTailFlags : flags.length = axes.length := by
            simp only [List.length_cons] at hFlags
            omega
          simp only [List.map_cons, cartesianIndices, List.mem_flatMap, List.mem_map] at hIndex
          obtain ⟨tail, hTailIndex, i, hi, rfl⟩ := hIndex
          have hReflectedTail := ih firsts lasts flags tail hTail hTailFlags hTailIndex
          have hReflectedHead : (if flag then (last + first) - i else i) ∈ ops.indices axis := by
            cases flag with
            | false => exact hi
            | true =>
              rw [hRange axis first last hHead.1 hHead.2] at hi ⊢
              exact amReflectedRange first last i hi
          simp only [reflectedIndex, List.zip_cons_cons, List.map_cons]
          apply List.mem_flatMap.mpr
          refine ⟨_, hReflectedTail, ?_⟩
          exact List.mem_map.mpr ⟨_, hReflectedHead, rfl⟩

 theorem MemsafetyArraymathReverse_proven : JuliaLean.Proofs.base.arraymath.ReverseInBounds := by
  intro Store A V Axis ops rank dims array state output state' axes firsts lasts index
    hOps _ _ _ hEnds hFirst _ _ hIndex
  refine ⟨hIndex, ?_⟩
  apply amReflectedCartesian ops.index hOps.1 axes firsts lasts _ index hEnds ?_ hIndex
  simp only [List.length_map, dimensions, List.length_range]
  have hAxes := hEnds.1
  omega

 theorem amNodupSubsetPermutation {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List α) (hNo : xs.Nodup) (hSub : xs ⊆ ys)
    (hLen : xs.length = ys.length) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.eq_nil_of_length_eq_zero hLen.symm
    subst ys
    exact .nil
  | cons a xs ih =>
    have hNo' := List.nodup_cons.mp hNo
    have ha : a ∈ ys := hSub (List.mem_cons_self ..)
    have hSub' : xs ⊆ ys.erase a := by
      intro x hx
      have hxa : x ≠ a := by
        intro he
        exact hNo'.1 (he ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hSub (List.mem_cons_of_mem _ hx))
    have hLen' : xs.length = (ys.erase a).length := by
      rw [List.length_erase_of_mem ha]
      simp only [List.length_cons] at hLen
      omega
    exact ((ih (ys.erase a) hNo'.2 hSub' hLen').cons a).trans
      (List.perm_cons_erase ha).symm

 theorem amDimensionValue (rank k : Nat) (hRank : rank < 2 ^ 63) (hk : k < rank) :
    (JuliaLean.base.abstractarray.int (Int.ofNat (k + 1))).val = Int.ofNat (k + 1) := by
  change (JInt.wrap .i64 (Int.ofNat (k + 1))).val = _
  apply amIntWrapValue
  simp only [IntTy.min, IntTy.max, IntTy.signed, IntTy.bits, ite_true]
  change -(9223372036854775808 : Int) ≤ (k : Int) + 1 ∧
    (k : Int) + 1 ≤ 9223372036854775807
  omega

 theorem amDimensionsNodup (rank : Nat) (hRank : rank < 2 ^ 63) :
    (dimensions rank).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj hij
  have hir : i < rank := by simpa only [dimensions, List.length_map, List.length_range] using hi
  have hjr : j < rank := by simpa only [dimensions, List.length_map, List.length_range] using hj
  have hv := congrArg Subtype.val hij
  simp only [dimensions, List.getElem_map, List.getElem_range] at hv
  rw [amDimensionValue rank i hRank hir, amDimensionValue rank j hRank hjr] at hv
  change (i : Int) + 1 = (j : Int) + 1 at hv
  omega

 theorem amDimensionBounds (rank : Nat) (hRank : rank < 2 ^ 63)
    (d : JuliaLean.base.arraymath.I64) (hd : d ∈ dimensions rank) :
    1 ≤ d.val ∧ d.val ≤ (rank : Int) := by
  simp only [dimensions, List.mem_map, List.mem_range] at hd
  obtain ⟨k, hk, rfl⟩ := hd
  rw [amDimensionValue rank k hRank hk]
  change 1 ≤ (k : Int) + 1 ∧ (k : Int) + 1 ≤ (rank : Int)
  omega

 theorem amCountMembershipValid (rank : Nat) (dims : List JuliaLean.base.arraymath.I64)
    (hRank : rank < 2 ^ 63)
    (hCount : dims.length = (dimensions rank).countP (fun d => dims.contains d)) :
    JuliaLean.Proofs.base.arraymath.Round3.ValidDimensionSet rank dims := by
  let selected := (dimensions rank).filter fun d => dims.contains d
  have hNo : selected.Nodup := List.Pairwise.filter _ (amDimensionsNodup rank hRank)
  have hSub : selected ⊆ dims := by
    intro d hd
    exact List.contains_iff_mem.mp (List.mem_filter.mp hd).2
  have hLen : selected.length = dims.length := by
    simpa only [selected, List.countP_eq_length_filter] using hCount.symm
  have hp := amNodupSubsetPermutation selected dims hNo hSub hLen
  refine ⟨hp.nodup_iff.mp hNo, ?_⟩
  intro d hd
  have hs : d ∈ selected := hp.mem_iff.mpr hd
  exact amDimensionBounds rank hRank d (List.mem_filter.mp hs).1

 theorem amCountTrueMap {α : Type} (f : α → Bool) (xs : List α) :
    (xs.map f).count true = xs.countP f := by
  simp only [List.count_eq_countP, List.countP_map, Function.comp_def]
  have hf : (fun x => f x == true) = f := by
    funext x
    cases f x <;> rfl
  rw [hf]

 theorem ArraymathReverseInvalidDimensions_proven :
    JuliaLean.Proofs.base.arraymath.Round3.ReverseInvalidDimensionsCorrect := by
  intro Store A V Axis ops rank a dims state hRank _ _ hInvalid
  have hNotNil : dims ≠ [] := by
    intro he
    apply hInvalid
    subst dims
    refine ⟨List.nodup_nil, ?_⟩
    intro d hd
    cases hd
  have hCount : dims.length ≠
      ((dimensions rank).map fun d => dims.contains d).count true := by
    intro hc
    apply hInvalid
    apply amCountMembershipValid rank dims hRank
    simpa only [amCountTrueMap] using hc
  have hCore : StateT.run
      (reverseBangCore (JuliaLean.Proofs.base.arraymath.Round3.precheckOps ops) rank a dims) state =
      .error (.julia (.argumentError
        ("invalid dimensions " ++ ops.showDims dims ++ " in reverse!"))) := by
    cases dims with
    | nil => exact False.elim (hNotNil rfl)
    | cons d ds =>
      have hCheck : (rank < (d :: ds).length ||
          (d :: ds).length != ((dimensions rank).map fun e => (d :: ds).contains e).count true) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_iff, bne_iff_ne]
        exact Or.inr hCount
      simp only [reverseBangCore, hCheck, ite_true,
        JuliaLean.Proofs.base.arraymath.Round3.precheckOps, StateT.run]
  refine ⟨"invalid dimensions " ++ ops.showDims dims ++ " in reverse!", ?_⟩
  unfold JuliaLean.Proofs.base.arraymath.Round3.genericTupleReverse
  split <;> simpa only [JuliaLean.base.array.reverseDims, reverseBang] using hCore

end JuliaLean.ChatGPT.Batch4.Group22

namespace JuliaLean.Proofs.base.arraymath

open JuliaLean.Registry
def entries : List Entry := [
  { (entry "arraymath-broadcast-same-rank"
    ["_broadcast_preserving_zero_d(f,Array{<:Any,N},Array{<:Any,N},Array{<:Any,N}...)"]
    "Equal-rank `Array` mapping returns the function applied to corresponding input elements."
    "base/arraymath.jl:12-14; map contract"
    ``ArrayBinaryPointwise) with status := .todo, thm := none, notes := "Arbitrary mapper law constrains successful results only; required successful output is not guaranteed. Statement-defect review only; no Julia refutation." },
  { (entry "arraymath-broadcast-rank"
    ["_broadcast_preserving_zero_d(f,Array,Array,Array...)"]
    "For shape-compatible inputs of any rank, the helper selects a maximal-rank shape, preserves element values while reshaping lower-rank arrays, and maps to that shape."
    "base/arraymath.jl:16-25; reshape and map contracts"
    ``BroadcastRankShapeAndValues) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ArraymathBroadcastRank_proven },
  { (entry "arraymath-arithmetic-pointwise"
    ["+(::Array)", "+(::Number,::AbstractArray)", "*(::Number,::AbstractArray)",
     "\\(::Number,::AbstractArray)", "/(::AbstractArray,::Number)", "*(::AbstractArray,::Number)"]
    "Unary plus preserves every element; scalar-array arithmetic applies its operation with the scalar on the source-defined side."
    "base/arraymath.jl:27-33,42,52-59; map and Fix1/Fix2 contracts"
    ``ArrayArithmeticPointwise) with status := .todo, thm := none, notes := "Conditional map law lacks totality; scalar premise uses independent apply while execution uses f, without identification." },
  { (entry "arraymath-abstractarray-binary-pointwise"
    ["+(::AbstractArray,::AbstractArray)", "-(::AbstractArray,::AbstractArray)"]
    "For compatible AbstractArrays, addition and subtraction apply their element operator at every shared index."
    "base/arraymath.jl:35-41; broadcast contract"
    ``AbstractArrayBinaryPointwise) with status := .todo, thm := none, notes := "Arbitrary broadcast law is conditional on success; existential output is not guaranteed. Statement-defect review only." },
  { (entry "arraymath-mixed-rank-pointwise"
    ["+(::AbstractArray,::AbstractArray)", "-(::AbstractArray,::AbstractArray)",
     "+(::Array,::Array,::Array...)"]
    "Unequal-rank AbstractArray addition and subtraction use the broadcast fallback; variadic Array addition reshapes lower-rank inputs to a maximal-rank shape and returns mapped values at that shape."
    "base/arraymath.jl:35-50; broadcast, size, mapreduce, and reshape contracts"
    ``MixedRankArrayArithmeticPointwise) with status := .todo, thm := none, notes := "Binary broadcast and variadic mapper/reshape callbacks lack success guarantees. Conditional helpers cannot settle the conjunction." },
  { (entry "arraymath-variadic-pointwise"
    ["+(::Array,::Array,::Array...)"]
    "For compatible equal-rank arrays, variadic addition applies `+` to every corresponding input element."
    "base/arraymath.jl:44-50; map contract"
    ``ArrayVariadicPointwise) with status := .todo, thm := none, notes := "Conditional map law does not guarantee the output required by the full frozen formula." },
  { (entry "arraymath-shape-errors"
    ["+(::Array,::Array,::Array...)"]
    "Variadic Array addition returns the first shape-promotion error in input order before mapping."
    "base/arraymath.jl:44-50; promote_shape compatibility contract"
    ``ArrayShapeErrors) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ArraymathShapeErrors_proven },
  { (entry "arraymath-abstractarray-shape-errors"
    ["+(::AbstractArray,::AbstractArray)", "-(::AbstractArray,::AbstractArray)"]
    "AbstractArray addition and subtraction return the first promote_shape error before broadcasting."
    "base/arraymath.jl:35-41"
    ``AbstractArrayShapeErrors) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ArraymathAbstractarrayShapeErrors_proven },
  { (entry "arraymath-reverse-coordinate"
    ["reverse!(::AbstractArray; dims)", "_reverse!(::AbstractArray,::Colon)",
     "_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "For valid dimension tuples, reverse! places every source value at its reflected Cartesian coordinate, including recursive odd middle slices."
    "base/arraymath.jl:95-130; reverse! docstring and AbstractArray indexing laws"
    ``ReverseCoordinateContract) with status := .todo, thm := none, notes := "Abstract reversal laws omit faithful liftResult, consistent metadata, pure successful division, and persistent view frame conditions." },
  { (entry "arraymath-reverse-invalid-dimensions"
    ["_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "On the complete dispatch domain of the generic native Int tuple reversal method, repeated dimensions or dimensions outside 1:rank throw ArgumentError. The independent condition is Nodup plus mathematical range membership, not the implementation membership-count branch; bounds rank, tuple length <2^63 cover their complete nonnegative native-Int range. The precheck only converts k+1<=rank, while membership count/length comparisons stay Nat; no doubled length or offset arithmetic is reached. The public arraymath.reverseBang wrapper is selected off rank one and array.reverseDims on rank one. Rank-one singleton tuples select a distinct forwarding overload (base/arraymath.jl:133) and retain the frozen vector scalar-dimension contract multidimcov-array-v2-reverse-dims; that forwarding method is not claimed as generic-core execution. Later heap callbacks are universally quantified, never assumed correct or passed an expected answer."
    "base/arraymath.jl:103,107-113,133; base/array.jl:2264-2272; docs/invariant: base/arraymath.jl:63-68,95-101,108-113 and doc/src/manual/arrays.md:38-43"
    ``Round3.ReverseInvalidDimensionsCorrect) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ArraymathReverseInvalidDimensions_proven },
  { (entry "arraymath-reverse-input-preserved"
    ["reverse(::AbstractArray; dims)", "_reverse(A,dims)"]
    "Non-mutating reverse returns reflected values from a fresh content-preserving copy and leaves every source value unchanged."
    "base/arraymath.jl:63-93; reverse docstring and copy/indexing laws"
    ``ReversePreservesInput) with status := .todo, thm := none, notes := "Abstract effect laws omit pure metadata lifting and persistent source/copy frame conditions; no full-domain proof." },
  { (entry "arraymath-reverse-dimension-conversion"
    ["_reverse!(A,::Integer)", "_reverse!(A,::NTuple{M,Integer})"]
    "Integer-to-Int conversion errors occur before reversal and are returned unchanged."
    "base/arraymath.jl:105-106"
    ``ReverseDimensionConversionErrors) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.ArraymathReverseDimensionConversion_proven },
  { (entry "arraymath-reverse-conversion-success"
    ["_reverse!(A,dim::Integer)", "_reverse!(A,dims::NTuple{M,Integer})",
     "_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "Successful dimension conversion reaches reversal and returns values at their reflected Cartesian coordinates."
    "base/arraymath.jl:105-107; AbstractArray indexing laws"
    ``ReverseDimensionConversionSuccess) with status := .todo, thm := none, notes := "Successful conversion cannot repair missing reversal-effect laws; full frozen coordinate conclusion remains unsupported." },
  { (entry "arraymath-rotation-coordinates"
    ["rotl90(::AbstractMatrix)", "rotr90(::AbstractMatrix)", "rot180(::AbstractMatrix)"]
    "Each matrix rotation preserves source values at its documented reflected output coordinates, including offset axes."
    "base/arraymath.jl:136-217; matrix allocation and indexing laws"
    ``MatrixRotationCoordinates) with status := .todo, thm := none, notes := "Abstract allocation/setter laws do not preserve source values; metadata lifting is also unconstrained." },
  { (entry "arraymath-counted-rotations"
    ["rotl90(::AbstractMatrix,::Integer)", "rotr90(::AbstractMatrix,::Integer)",
     "rot180(::AbstractMatrix,::Integer)"]
    "Quarter-turn counts select the orientation modulo four; half-turn counts select rotation when odd and a fresh content-preserving copy when even."
    "base/arraymath.jl:218-317; counted-rotation docstrings and copy laws"
    ``CountedRotationCoordinates) with status := .todo, thm := none, notes := "Arbitrary successful modulo/negation effects can modify the matrix; current laws only constrain original-store outcomes." },
  { (entry "memsafety-arraymath-reverse"
    ["_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "For each valid Cartesian index, `reverseBangCore`'s direct access and actual `reflectedIndex` access remain inside the input axes."
    "memory-safety invariant; base/arraymath.jl:107-130; model reflectedIndex"
    ``ReverseInBounds) with status := .proven, thm := some ``JuliaLean.ChatGPT.Batch4.Group22.MemsafetyArraymathReverse_proven }
]

end JuliaLean.Proofs.base.arraymath
