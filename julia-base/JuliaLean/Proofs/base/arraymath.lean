import JuliaLean.base.array
import JuliaLean.base.abstractarray
import JuliaLean.base.arraymath
import JuliaLean.Registry.Types

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

def entries : List Entry := [
  entry "arraymath-broadcast-same-rank"
    ["_broadcast_preserving_zero_d(f,Array{<:Any,N},Array{<:Any,N},Array{<:Any,N}...)"]
    "Equal-rank `Array` mapping returns the function applied to corresponding input elements."
    "base/arraymath.jl:12-14; map contract"
    ``ArrayBinaryPointwise,
  entry "arraymath-broadcast-rank"
    ["_broadcast_preserving_zero_d(f,Array,Array,Array...)"]
    "For shape-compatible inputs of any rank, the helper selects a maximal-rank shape, preserves element values while reshaping lower-rank arrays, and maps to that shape."
    "base/arraymath.jl:16-25; reshape and map contracts"
    ``BroadcastRankShapeAndValues,
  entry "arraymath-arithmetic-pointwise"
    ["+(::Array)", "+(::Number,::AbstractArray)", "*(::Number,::AbstractArray)",
     "\\(::Number,::AbstractArray)", "/(::AbstractArray,::Number)", "*(::AbstractArray,::Number)"]
    "Unary plus preserves every element; scalar-array arithmetic applies its operation with the scalar on the source-defined side."
    "base/arraymath.jl:27-33,42,52-59; map and Fix1/Fix2 contracts"
    ``ArrayArithmeticPointwise,
  entry "arraymath-abstractarray-binary-pointwise"
    ["+(::AbstractArray,::AbstractArray)", "-(::AbstractArray,::AbstractArray)"]
    "For compatible AbstractArrays, addition and subtraction apply their element operator at every shared index."
    "base/arraymath.jl:35-41; broadcast contract"
    ``AbstractArrayBinaryPointwise,
  entry "arraymath-mixed-rank-pointwise"
    ["+(::AbstractArray,::AbstractArray)", "-(::AbstractArray,::AbstractArray)",
     "+(::Array,::Array,::Array...)"]
    "Unequal-rank AbstractArray addition and subtraction use the broadcast fallback; variadic Array addition reshapes lower-rank inputs to a maximal-rank shape and returns mapped values at that shape."
    "base/arraymath.jl:35-50; broadcast, size, mapreduce, and reshape contracts"
    ``MixedRankArrayArithmeticPointwise,
  entry "arraymath-variadic-pointwise"
    ["+(::Array,::Array,::Array...)"]
    "For compatible equal-rank arrays, variadic addition applies `+` to every corresponding input element."
    "base/arraymath.jl:44-50; map contract"
    ``ArrayVariadicPointwise,
  entry "arraymath-shape-errors"
    ["+(::Array,::Array,::Array...)"]
    "Variadic Array addition returns the first shape-promotion error in input order before mapping."
    "base/arraymath.jl:44-50; promote_shape compatibility contract"
    ``ArrayShapeErrors,
  entry "arraymath-abstractarray-shape-errors"
    ["+(::AbstractArray,::AbstractArray)", "-(::AbstractArray,::AbstractArray)"]
    "AbstractArray addition and subtraction return the first promote_shape error before broadcasting."
    "base/arraymath.jl:35-41"
    ``AbstractArrayShapeErrors,
  entry "arraymath-reverse-coordinate"
    ["reverse!(::AbstractArray; dims)", "_reverse!(::AbstractArray,::Colon)",
     "_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "For valid dimension tuples, reverse! places every source value at its reflected Cartesian coordinate, including recursive odd middle slices."
    "base/arraymath.jl:95-130; reverse! docstring and AbstractArray indexing laws"
    ``ReverseCoordinateContract,
  entry "arraymath-reverse-invalid-dimensions"
    ["_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "Invalid nonempty dimension tuples throw ArgumentError."
    "base/arraymath.jl:107-113"
    ``ReverseInvalidDimensions,
  entry "arraymath-reverse-input-preserved"
    ["reverse(::AbstractArray; dims)", "_reverse(A,dims)"]
    "Non-mutating reverse returns reflected values from a fresh content-preserving copy and leaves every source value unchanged."
    "base/arraymath.jl:63-93; reverse docstring and copy/indexing laws"
    ``ReversePreservesInput,
  entry "arraymath-reverse-dimension-conversion"
    ["_reverse!(A,::Integer)", "_reverse!(A,::NTuple{M,Integer})"]
    "Integer-to-Int conversion errors occur before reversal and are returned unchanged."
    "base/arraymath.jl:105-106"
    ``ReverseDimensionConversionErrors,
  entry "arraymath-reverse-conversion-success"
    ["_reverse!(A,dim::Integer)", "_reverse!(A,dims::NTuple{M,Integer})",
     "_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "Successful dimension conversion reaches reversal and returns values at their reflected Cartesian coordinates."
    "base/arraymath.jl:105-107; AbstractArray indexing laws"
    ``ReverseDimensionConversionSuccess,
  entry "arraymath-rotation-coordinates"
    ["rotl90(::AbstractMatrix)", "rotr90(::AbstractMatrix)", "rot180(::AbstractMatrix)"]
    "Each matrix rotation preserves source values at its documented reflected output coordinates, including offset axes."
    "base/arraymath.jl:136-217; matrix allocation and indexing laws"
    ``MatrixRotationCoordinates,
  entry "arraymath-counted-rotations"
    ["rotl90(::AbstractMatrix,::Integer)", "rotr90(::AbstractMatrix,::Integer)",
     "rot180(::AbstractMatrix,::Integer)"]
    "Quarter-turn counts select the orientation modulo four; half-turn counts select rotation when odd and a fresh content-preserving copy when even."
    "base/arraymath.jl:218-317; counted-rotation docstrings and copy laws"
    ``CountedRotationCoordinates,
  entry "memsafety-arraymath-reverse"
    ["_reverse!(::AbstractArray,::NTuple{M,Int})"]
    "For each valid Cartesian index, `reverseBangCore`'s direct access and actual `reflectedIndex` access remain inside the input axes."
    "memory-safety invariant; base/arraymath.jl:107-130; model reflectedIndex"
    ``ReverseInBounds
]

end JuliaLean.Proofs.base.arraymath
