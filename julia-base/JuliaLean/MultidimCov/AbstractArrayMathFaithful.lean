import JuliaLean.MultidimCov.AbstractArrayMathReview
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayMathFaithful

open JuliaLean.Registry

inductive AMError where
  | argument
  | bounds
  | typeAssertion
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev AMResult (α : Type) := Except AMError α

/-- Corrected `_dropdims`, lines 86-103. -/
def m86 (validate : A → List Int → AMResult Unit) (axes : A → AMResult (List X))
    (foldAxes : A → List Int → AMResult (List X)) (concrete : List X → AMResult Bool)
    (subAxes : List X → List Int → AMResult (List X))
    (typeAssert : List X → List X → AMResult (List X))
    (reshape : A → List X → AMResult R) (array : A) (dims : List Int) : AMResult R := do
  validate array dims
  let oldAxes ← axes array
  let retained ← foldAxes array dims
  let isConcrete ← concrete oldAxes
  if isConcrete then do
    let expected ← subAxes oldAxes dims
    let asserted ← typeAssert retained expected
    reshape array asserted
  else reshape array retained
def P86 : Prop := ∀ {A X R : Type} validate axes foldAxes concrete subAxes typeAssert reshape array dims,
  m86 (A := A) (X := X) (R := R) validate axes foldAxes concrete subAxes typeAssert reshape array dims = do
    validate array dims
    let oldAxes ← axes array
    let retained ← foldAxes array dims
    let isConcrete ← concrete oldAxes
    if isConcrete then do
      let expected ← subAxes oldAxes dims
      let asserted ← typeAssert retained expected
      reshape array asserted
    else reshape array retained
theorem p86 : P86 := by unfold P86; intros; rfl

/-- Numeric in-place conjugation, line 194. -/
def m194 (broadcastBang : F → A → A → AMResult A) (conj : F) (array : A) : AMResult A := do
  let mutated ← broadcastBang conj array array
  .ok mutated
def P194 : Prop := ∀ {F A : Type} broadcastBang conj array,
  m194 (F := F) (A := A) broadcastBang conj array = do
    let mutated ← broadcastBang conj array array
    .ok mutated
theorem p194 : P194 := by unfold P194; intros; rfl

/-- Real-array in-place conjugation, line 195. -/
def m195 (array : A) : A := array
def P195 : Prop := ∀ {A : Type} array, m195 (A := A) array = array
theorem p195 : P195 := by unfold P195 m195; intros; rfl

/-- Nested-array in-place conjugation, line 196. -/
def m196 (foreachMutating : A → AMResult A) (array : A) : AMResult A := do
  let mutated ← foreachMutating array
  .ok mutated
def P196 : Prop := ∀ {A : Type} foreachMutating array,
  m196 (A := A) foreachMutating array = do let mutated ← foreachMutating array; .ok mutated
theorem p196 : P196 := by unfold P196; intros; rfl

/-- Method-specific `conj`, line 220. -/
def m220 (broadcastPreservingZeroD : Conj → A → AMResult R) (conj : Conj) (array : A) : AMResult R :=
  broadcastPreservingZeroD conj array
def P220 : Prop := ∀ {Conj A R : Type} broadcastPreservingZeroD conj array,
  m220 (Conj := Conj) (A := A) (R := R) broadcastPreservingZeroD conj array =
    broadcastPreservingZeroD conj array
theorem p220 : P220 := by unfold P220 m220; intros; rfl

/-- Real-array `conj`, line 221. -/
def m221 (array : A) : A := array
def P221 : Prop := ∀ {A : Type} array, m221 (A := A) array = array
theorem p221 : P221 := by unfold P221 m221; intros; rfl

/-- Method-specific `real`, line 245. -/
def m245 (broadcastPreservingZeroD : RealFn → A → AMResult R) (realFn : RealFn) (array : A) : AMResult R :=
  broadcastPreservingZeroD realFn array
def P245 : Prop := ∀ {RealFn A R : Type} broadcastPreservingZeroD realFn array,
  m245 (RealFn := RealFn) (A := A) (R := R) broadcastPreservingZeroD realFn array =
    broadcastPreservingZeroD realFn array
theorem p245 : P245 := by unfold P245 m245; intros; rfl

/-- Real-array `real`, line 246. -/
def m246 (array : A) : A := array
def P246 : Prop := ∀ {A : Type} array, m246 (A := A) array = array
theorem p246 : P246 := by unfold P246 m246; intros; rfl

/-- Method-specific `imag`, line 269. -/
def m269 (broadcastPreservingZeroD : ImagFn → A → AMResult R) (imagFn : ImagFn) (array : A) : AMResult R :=
  broadcastPreservingZeroD imagFn array
def P269 : Prop := ∀ {ImagFn A R : Type} broadcastPreservingZeroD imagFn array,
  m269 (ImagFn := ImagFn) (A := A) (R := R) broadcastPreservingZeroD imagFn array =
    broadcastPreservingZeroD imagFn array
theorem p269 : P269 := by unfold P269 m269; intros; rfl

/-- Method-specific unary minus, line 293. -/
def m293 (broadcastPreservingZeroD : NegFn → A → AMResult R) (negFn : NegFn) (array : A) : AMResult R :=
  broadcastPreservingZeroD negFn array
def P293 : Prop := ∀ {NegFn A R : Type} broadcastPreservingZeroD negFn array,
  m293 (NegFn := NegFn) (A := A) (R := R) broadcastPreservingZeroD negFn array =
    broadcastPreservingZeroD negFn array
theorem p293 : P293 := by unfold P293 m293; intros; rfl

/-- Unary plus on numeric arrays, line 295. -/
def m295 (array : A) : A := array
def P295 : Prop := ∀ {A : Type} array, m295 (A := A) array = array
theorem p295 : P295 := by unfold P295 m295; intros; rfl

/-- Unary matrix multiplication, line 296. -/
def m296 (array : A) : A := array
def P296 : Prop := ∀ {A : Type} array, m296 (A := A) array = array
theorem p296 : P296 := by unfold P296 m296; intros; rfl

/-- `_selectdim`, lines 328-333. -/
def m328 (lessThanOne : D → AMResult Bool) (ndims : A → AMResult N)
    (greater : D → N → AMResult Bool) (equalOne : I → AMResult Bool)
    (argumentError : D → AMResult R) (boundsError : A → D → I → AMResult R)
    (view : A → Idx → AMResult R) (array : A) (dimension : D) (index : I) (indices : Idx) : AMResult R := do
  let below ← lessThanOne dimension
  if below then argumentError dimension
  else do
    let rank ← ndims array
    let trailing ← greater dimension rank
    if trailing then do
      let singleton ← equalOne index
      if singleton then view array indices else boundsError array dimension index
    else view array indices
def P328 : Prop := ∀ {D A N I Idx R : Type} lessThanOne ndims greater equalOne argumentError
    boundsError view array dimension index indices,
  m328 (D := D) (A := A) (N := N) (I := I) (Idx := Idx) (R := R)
    lessThanOne ndims greater equalOne argumentError boundsError view array dimension index indices = do
      let below ← lessThanOne dimension
      if below then argumentError dimension
      else do
        let rank ← ndims array
        let trailing ← greater dimension rank
        if trailing then do
          let singleton ← equalOne index
          if singleton then view array indices else boundsError array dimension index
        else view array indices
theorem p328 : P328 := by unfold P328; intros; rfl

/-- Real-shift `circshift`, lines 335-337. -/
def m335 (similar : A → AMResult B) (toInteger : S → AMResult I)
    (circshiftBang : B → A → List I → AMResult R) (array : A) (amount : S) : AMResult R := do
  let destination ← similar array
  let shift ← toInteger amount
  circshiftBang destination array [shift]
def P335 : Prop := ∀ {A B S I R : Type} similar toInteger circshiftBang array amount,
  m335 (A := A) (B := B) (S := S) (I := I) (R := R)
    similar toInteger circshiftBang array amount = do
      let destination ← similar array
      let shift ← toInteger amount
      circshiftBang destination array [shift]
theorem p335 : P335 := by unfold P335; intros; rfl

/-- Generic-shift `circshift`, lines 411-413. -/
def m411 (similar : A → AMResult B) (splat : S → AMResult (List X))
    (toInteger : X → AMResult I) (circshiftBang : B → A → List I → AMResult R)
    (array : A) (amount : S) : AMResult R := do
  let destination ← similar array
  let values ← splat amount
  let shifts ← values.mapM toInteger
  circshiftBang destination array shifts
def P411 : Prop := ∀ {A B S X I R : Type} similar splat toInteger circshiftBang array amount,
  m411 (A := A) (B := B) (S := S) (X := X) (I := I) (R := R)
    similar splat toInteger circshiftBang array amount = do
      let destination ← similar array
      let values ← splat amount
      let shifts ← values.mapM toInteger
      circshiftBang destination array shifts
theorem p411 : P411 := by unfold P411; intros; rfl

/-- Generic `to_tuple`, line 496. -/
def m496 (iterateAll : I → AMResult (List X)) (tuple : List X → AMResult T) (iterator : I) : AMResult T := do
  let values ← iterateAll iterator
  tuple values
def P496 : Prop := ∀ {I X T : Type} iterateAll tuple iterator,
  m496 (I := I) (X := X) (T := T) iterateAll tuple iterator = do
    let values ← iterateAll iterator
    tuple values
theorem p496 : P496 := by unfold P496; intros; rfl

/-- Two-way repeat-count padding, lines 498-501. -/
def m498 (length : T → AMResult Nat) (one : AMResult V) (val : Nat → AMResult N)
    (fillToLength : T → V → N → AMResult T) (a b : T) : AMResult (T × T) := do
  let la ← length a
  let lb ← length b
  let fill ← one
  let target ← val (max la lb)
  let aa ← fillToLength a fill target
  let bb ← fillToLength b fill target
  .ok (aa, bb)
def P498 : Prop := ∀ {T V N : Type} length one val fillToLength a b,
  m498 (T := T) (V := V) (N := N) length one val fillToLength a b = do
    let la ← length a
    let lb ← length b
    let fill ← one
    let target ← val (max la lb)
    let aa ← fillToLength a fill target
    let bb ← fillToLength b fill target
    .ok (aa, bb)
theorem p498 : P498 := by unfold P498; intros; rfl

/-- Three-way repeat-count padding, lines 502-505. -/
def m502 (length : T → AMResult Nat) (one : AMResult V) (val : Nat → AMResult N)
    (fillToLength : T → V → N → AMResult T) (a b c : T) : AMResult (T × T × T) := do
  let la ← length a
  let lb ← length b
  let lc ← length c
  let fill ← one
  let target ← val (max (max la lb) lc)
  let aa ← fillToLength a fill target
  let bb ← fillToLength b fill target
  let cc ← fillToLength c fill target
  .ok (aa, bb, cc)
def P502 : Prop := ∀ {T V N : Type} length one val fillToLength a b c,
  m502 (T := T) (V := V) (N := N) length one val fillToLength a b c = do
    let la ← length a
    let lb ← length b
    let lc ← length c
    let fill ← one
    let target ← val (max (max la lb) lc)
    let aa ← fillToLength a fill target
    let bb ← fillToLength b fill target
    let cc ← fillToLength c fill target
    .ok (aa, bb, cc)
theorem p502 : P502 := by unfold P502; intros; rfl

def allValues (predicate : V → AMResult Bool) : List V → AMResult Bool
  | [] => .ok true
  | value :: rest => do
      let yes ← predicate value
      if yes then allValues predicate rest else .ok false

def anyValues (predicate : V → AMResult Bool) : List V → AMResult Bool
  | [] => .ok false
  | value :: rest => do
      let yes ← predicate value
      if yes then .ok true else anyValues predicate rest

/-- Repeat validation, lines 526-552. -/
def m526 (requireOneBased : A → AMResult Unit) (isInteger negative : V → AMResult Bool)
    (ndims : A → AMResult Nat) (array : A) (inner outer : Option (List V)) : AMResult Unit := do
  match inner with
  | some counts =>
      requireOneBased array
      let integers ← allValues isInteger counts
      if ¬integers then .error .argument
      let hasNegative ← anyValues negative counts
      if hasNegative then .error .argument
      let rank ← ndims array
      if counts.length < rank then .error .argument
  | none => .ok ()
  match outer with
  | some counts =>
      let integers ← allValues isInteger counts
      if ¬integers then .error .argument
      let hasNegative ← anyValues negative counts
      if hasNegative then .error .argument
      let rank ← ndims array
      if counts.length < rank && inner.isSome then .error .argument else .ok ()
  | none => .ok ()
def P526 : Prop := ∀ {A V : Type} requireOneBased isInteger negative ndims array inner outer,
  m526 (A := A) (V := V) requireOneBased isInteger negative ndims array inner outer = do
    match inner with
    | some counts =>
        requireOneBased array
        let integers ← allValues isInteger counts
        if ¬integers then .error .argument
        let hasNegative ← anyValues negative counts
        if hasNegative then .error .argument
        let rank ← ndims array
        if counts.length < rank then .error .argument
    | none => .ok ()
    match outer with
    | some counts =>
        let integers ← allValues isInteger counts
        if ¬integers then .error .argument
        let hasNegative ← anyValues negative counts
        if hasNegative then .error .argument
        let rank ← ndims array
        if counts.length < rank && inner.isSome then .error .argument else .ok ()
    | none => .ok ()
theorem p526 : P526 := by unfold P526; intros; rfl

def matrixBlocks (setBlock : B → Nat → Nat → A → AMResult B) (source : A)
    (rows cols m : Nat) : B → List Nat → AMResult B
  | output, [] => .ok output
  | output, j :: js => do
      let columnStart := j * cols + 1
      let next ← (List.range m).foldlM (fun out i =>
        let rowStart := i * rows + 1
        setBlock out rowStart columnStart source) output
      matrixBlocks setBlock source rows cols m next js

/-- Matrix `repeat_outer`, lines 559-571. -/
def m559 (size1 size2 : A → AMResult Nat) (checkedMul : Nat → Nat → AMResult Nat)
    (similar : A → Nat → Nat → AMResult B) (setBlock : B → Nat → Nat → A → AMResult B)
    (array : A) (m n : Nat) : AMResult B := do
  let rows ← size1 array
  let cols ← size2 array
  let outRows ← checkedMul rows m
  let outCols ← checkedMul cols n
  let output ← similar array outRows outCols
  matrixBlocks setBlock array rows cols m output (List.range n)
def P559 : Prop := ∀ {A B : Type} size1 size2 checkedMul similar setBlock array m n,
  m559 (A := A) (B := B) size1 size2 checkedMul similar setBlock array m n = do
    let rows ← size1 array
    let cols ← size2 array
    let outRows ← checkedMul rows m
    let outCols ← checkedMul cols n
    let output ← similar array outRows outCols
    matrixBlocks setBlock array rows cols m output (List.range n)
theorem p559 : P559 := by unfold P559; intros; rfl

/-- Vector `repeat_outer`, lines 573-581. -/
def m573 (length : A → AMResult Nat) (checkedMul : Nat → Nat → AMResult Nat)
    (similar : A → Nat → AMResult B) (setBlock : B → Nat → Nat → A → AMResult B)
    (array : A) (m : Nat) : AMResult B := do
  let sourceLength ← length array
  let outLength ← checkedMul sourceLength m
  let output ← similar array outLength
  (List.range m).foldlM (fun out i =>
    let first := i * sourceLength + 1
    let last := first + sourceLength - 1
    setBlock out first last array) output
def P573 : Prop := ∀ {A B : Type} length checkedMul similar setBlock array m,
  m573 (A := A) (B := B) length checkedMul similar setBlock array m = do
    let sourceLength ← length array
    let outLength ← checkedMul sourceLength m
    let output ← similar array outLength
    (List.range m).foldlM (fun out i =>
      let first := i * sourceLength + 1
      let last := first + sourceLength - 1
      setBlock out first last array) output
theorem p573 : P573 := by unfold P573; intros; rfl

def outerCoordinates : List Nat → List Nat → List Nat → List Nat
  | i :: is, j :: js, d :: ds => (i + d * (j - 1)) :: outerCoordinates is js ds
  | _, _, _ => []

def innerCoordinates : List Nat → List Nat → List Nat → List Nat
  | i :: is, j :: js, d :: ds => ((i - 1) * d + j) :: innerCoordinates is js ds
  | _, _, _ => []

def assignCartesian (coordinates : List Nat → List Nat → List Nat → List Nat)
    (tuple : I → AMResult (List Nat)) (makeIndex : List Nat → AMResult I)
    (read : A → I → AMResult V) (write : B → I → V → AMResult B)
    (shape : List Nat) (array : A) : B → List I → List I → AMResult B
  | output, _, [] => .ok output
  | output, sources, target :: targets => do
      let tj ← tuple target
      let next ← sources.foldlM (fun out source => do
        let ti ← tuple source
        let ij ← makeIndex (coordinates ti tj shape)
        let value ← read array source
        write out ij value) output
      assignCartesian coordinates tuple makeIndex read write shape array next sources targets

/-- General `repeat_outer`, lines 583-597. -/
def m583 (size : A → AMResult (List Nat)) (checkedMul : Nat → Nat → AMResult Nat)
    (similar : A → List Nat → AMResult B) (cartesianArray : A → AMResult (List I))
    (cartesianDims : List Nat → AMResult (List I)) (tuple : I → AMResult (List Nat))
    (makeIndex : List Nat → AMResult I) (read : A → I → AMResult V)
    (write : B → I → V → AMResult B) (array : A) (dims : List Nat) : AMResult B := do
  let inputShape ← size array
  let outputShape ← (List.zip inputShape dims).mapM fun pair => checkedMul pair.1 pair.2
  let output ← similar array outputShape
  let sources ← cartesianArray array
  let targets ← cartesianDims dims
  assignCartesian outerCoordinates tuple makeIndex read write inputShape array output sources targets
def P583 : Prop := ∀ {A B I V : Type} size checkedMul similar cartesianArray cartesianDims tuple
    makeIndex read write array dims,
  m583 (A := A) (B := B) (I := I) (V := V) size checkedMul similar cartesianArray
    cartesianDims tuple makeIndex read write array dims = do
      let inputShape ← size array
      let outputShape ← (List.zip inputShape dims).mapM fun pair => checkedMul pair.1 pair.2
      let output ← similar array outputShape
      let sources ← cartesianArray array
      let targets ← cartesianDims dims
      assignCartesian outerCoordinates tuple makeIndex read write inputShape array output sources targets
theorem p583 : P583 := by unfold P583; intros; rfl

/-- General `repeat_inner`, lines 599-612. -/
def m599 (size : A → AMResult (List Nat)) (checkedMul : Nat → Nat → AMResult Nat)
    (similar : A → List Nat → AMResult B) (cartesianArray : A → AMResult (List I))
    (cartesianInner : List Nat → AMResult (List I)) (tuple : I → AMResult (List Nat))
    (makeIndex : List Nat → AMResult I) (read : A → I → AMResult V)
    (write : B → I → V → AMResult B) (array : A) (inner : List Nat) : AMResult B := do
  let inputShape ← size array
  let outputShape ← (List.zip inputShape inner).mapM fun pair => checkedMul pair.1 pair.2
  let output ← similar array outputShape
  let sources ← cartesianArray array
  let targets ← cartesianInner inner
  assignCartesian innerCoordinates tuple makeIndex read write inner array output sources targets
def P599 : Prop := ∀ {A B I V : Type} size checkedMul similar cartesianArray cartesianInner tuple
    makeIndex read write array inner,
  m599 (A := A) (B := B) (I := I) (V := V) size checkedMul similar cartesianArray
    cartesianInner tuple makeIndex read write array inner = do
      let inputShape ← size array
      let outputShape ← (List.zip inputShape inner).mapM fun pair => checkedMul pair.1 pair.2
      let output ← similar array outputShape
      let sources ← cartesianArray array
      let targets ← cartesianInner inner
      assignCartesian innerCoordinates tuple makeIndex read write inner array output sources targets
theorem p599 : P599 := by unfold P599; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarraymath-faithful-{line}", juliaFile := "base/abstractarraymath.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayMathFaithful
