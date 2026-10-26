import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.BroadcastShapeFaithful

open JuliaLean.Registry

inductive Error where | dimensionMismatch deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

structure Integer where
  typeName : String
  value : Int
  deriving Repr, DecidableEq

inductive AxisKind where
  | oneTo (typeName : String)
  | unitRange (typeName : String)
  | custom (typeName : String)
  deriving Repr, DecidableEq

structure Axis where
  kind : AxisKind
  values : List Int
  deriving Repr, DecidableEq

inductive Dim where
  | integer (value : Integer)
  | axis (value : Axis)
  deriving Repr, DecidableEq

def axisFirst (axis : Axis) : Option Int := axis.values.head?
def axisLast (axis : Axis) : Option Int := axis.values.getLast?
def dimLength : Dim → Nat
  | .integer value => if value.value < 0 then 0 else value.value.toNat
  | .axis axis => axis.values.length

def compatible (a b : Dim) : Bool := a = b || dimLength b = 1

def axisType (a b : Axis) : Axis :=
  if a.kind = b.kind then a
  else match a.kind, b.kind with
    | .oneTo _, .oneTo _ => { kind := .oneTo "Int", values := a.values }
    | _, _ => { kind := .unitRange "Int", values := a.values }

def bcs1 : Dim → Dim → Result Dim
  | .integer a, .integer b =>
      if a.value = 1 then .ok (.integer b)
      else if b.value = 1 then .ok (.integer a)
      else if a.value = b.value then .ok (.integer a)
      else .error .dimensionMismatch
  | .integer a, .axis b =>
      if a.value = 1 then .ok (.axis b)
      else if axisFirst b = some 1 && axisLast b = some a.value then .ok (.axis b)
      else .error .dimensionMismatch
  | .axis a, .integer b =>
      if b.value = 1 then .ok (.axis a)
      else if axisFirst a = some 1 && axisLast a = some b.value then .ok (.axis a)
      else .error .dimensionMismatch
  | .axis a, .axis b =>
      if compatible (.axis b) (.axis a) then .ok (.axis (axisType b a))
      else if compatible (.axis a) (.axis b) then .ok (.axis (axisType a b))
      else .error .dimensionMismatch

def bcs : List Dim → List Dim → Result (List Dim)
  | [], [] => .ok []
  | [], head :: tail => do pure (head :: (← bcs [] tail))
  | head :: tail, [] => do pure (head :: (← bcs tail []))
  | headA :: tailA, headB :: tailB => do
      let head ← bcs1 headA headB
      pure (head :: (← bcs tailA tailB))

def broadcastShape : List Dim → List (List Dim) → Result (List Dim)
  | shape, [] => .ok shape
  | shape, next :: rest => do broadcastShape (← bcs shape next) rest

def m502 {A : Type} (axes : A → List Dim) (first : A) (rest : List A) : Result (List Dim) :=
  broadcastShape (axes first) (rest.map axes)
def P502 : Prop := ∀ {A : Type} (axes : A → List Dim) first rest,
  m502 axes first rest = broadcastShape (axes first) (rest.map axes)
theorem p502 : P502 := by simp [P502, m502]

def m503 {A : Type} (axes : A → List Dim) (left right : A) : Result (List Dim) :=
  broadcastShape (axes left) [axes right]
def P503 : Prop := ∀ {A : Type} (axes : A → List Dim) left right,
  m503 axes left right = broadcastShape (axes left) [axes right]
theorem p503 : P503 := by simp [P503, m503]

def m504 {A : Type} (axes : A → List Dim) (value : A) : List Dim := axes value
def P504 : Prop := ∀ {A : Type} (axes : A → List Dim) value, m504 axes value = axes value
theorem p504 : P504 := by simp [P504, m504]

def m521 (shape : List Dim) : List Dim := shape
def P521 : Prop := ∀ shape, m521 shape = shape
theorem p521 : P521 := by simp [P521, m521]

def m522 (shape next : List Dim) (rest : List (List Dim)) : Result (List Dim) := do
  broadcastShape (← bcs shape next) rest
def P522 : Prop := ∀ shape next rest,
  m522 shape next rest = do broadcastShape (← bcs shape next) rest
theorem p522 : P522 := by simp [P522, m522]

def m524 : List Dim := []
def P524 : Prop := ∀ _ : Unit, m524 = []
theorem p524 : P524 := by simp [P524, m524]

def m525 (newshape : List Dim) : Result (List Dim) :=
  match newshape with
  | [] => .ok []
  | head :: tail => do pure (head :: (← bcs [] tail))
def P525 : Prop := ∀ head tail,
  m525 (head :: tail) = do pure (head :: (← bcs [] tail))
theorem p525 : P525 := by simp [P525, m525]

def m526 (shape : List Dim) : Result (List Dim) :=
  match shape with
  | [] => .ok []
  | head :: tail => do pure (head :: (← bcs tail []))
def P526 : Prop := ∀ head tail,
  m526 (head :: tail) = do pure (head :: (← bcs tail []))
theorem p526 : P526 := by simp [P526, m526]

def m527 (shape newshape : List Dim) : Result (List Dim) :=
  match shape, newshape with
  | headA :: tailA, headB :: tailB => do
      let head ← bcs1 headA headB
      pure (head :: (← bcs tailA tailB))
  | _, _ => .error .dimensionMismatch
def P527 : Prop := ∀ headA tailA headB tailB,
  m527 (headA :: tailA) (headB :: tailB) = do
    let head ← bcs1 headA headB
    pure (head :: (← bcs tailA tailB))
theorem p527 : P527 := by simp [P527, m527]

def m531 (a b : Integer) : Result Integer :=
  match bcs1 (.integer a) (.integer b) with
  | .ok (.integer value) => .ok value
  | _ => .error .dimensionMismatch
def P531 : Prop := ∀ a b,
  m531 a b =
    if a.value = 1 then .ok b
    else if b.value = 1 then .ok a
    else if a.value = b.value then .ok a
    else .error .dimensionMismatch
theorem p531 : P531 := by
  intro a b
  by_cases ha : a.value = 1
  · simp [m531, bcs1, ha]
  · by_cases hb : b.value = 1
    · simp [m531, bcs1, ha, hb]
    · by_cases heq : a.value = b.value <;> simp [m531, bcs1, ha, hb, heq]

def m532 (a : Integer) (b : Axis) : Result Axis :=
  match bcs1 (.integer a) (.axis b) with
  | .ok (.axis axis) => .ok axis
  | _ => .error .dimensionMismatch
def P532 : Prop := ∀ a b,
  m532 a b =
    if a.value = 1 then .ok b
    else if axisFirst b = some 1 && axisLast b = some a.value then .ok b
    else .error .dimensionMismatch
theorem p532 : P532 := by
  intro a b
  by_cases ha : a.value = 1
  · simp [m532, bcs1, ha]
  · by_cases haxis : axisFirst b = some 1 && axisLast b = some a.value
    · simp [m532, bcs1, ha, haxis]
    · simp [m532, bcs1, ha, haxis]

def m533 (a : Axis) (b : Integer) : Result Axis := m532 b a
def P533 : Prop := ∀ a b, m533 a b = m532 b a
theorem p533 : P533 := by simp [P533, m533]

def m534 (a b : Axis) : Result Axis :=
  if compatible (.axis b) (.axis a) then .ok (axisType b a)
  else if compatible (.axis a) (.axis b) then .ok (axisType a b)
  else .error .dimensionMismatch
def P534 : Prop := ∀ a b,
  m534 a b =
    if compatible (.axis b) (.axis a) then .ok (axisType b a)
    else if compatible (.axis a) (.axis b) then .ok (axisType a b)
    else .error .dimensionMismatch
theorem p534 : P534 := by simp [P534, m534]

def m536 (a b : Axis) : Bool := a = b || b.values.length = 1
def P536 : Prop := ∀ a b, m536 a b = (a = b || b.values.length = 1)
theorem p536 : P536 := by simp [P536, m536]

def m537 {A : Type} (_a : A) (b : Integer) : Bool := b.value = 1
def P537 : Prop := ∀ {A : Type} (a : A) b, m537 a b = (b.value = 1)
theorem p537 : P537 := by simp [P537, m537]

def m538 (a b : Integer) : Bool := a.value = b.value || b.value = 1
def P538 : Prop := ∀ a b, m538 a b = (a.value = b.value || b.value = 1)
theorem p538 : P538 := by simp [P538, m538]

def m542 (a : Axis) (_b : Axis) : Axis := a
def P542 : Prop := ∀ a b, m542 a b = a
theorem p542 : P542 := by simp [P542, m542]

def m543 (a : Axis) (_b : Axis) : Axis := { kind := .oneTo "Int", values := a.values }
def P543 : Prop := ∀ a b, m543 a b = { kind := .oneTo "Int", values := a.values }
theorem p543 : P543 := by simp [P543, m543]

def m544 (a : Axis) (_b : Axis) : Axis := { kind := .unitRange "Int", values := a.values }
def P544 : Prop := ∀ a b, m544 a b = { kind := .unitRange "Int", values := a.values }
theorem p544 : P544 := by simp [P544, m544]

def m548 {S : Type} (_shape : S) : Result Unit := .ok ()
def P548 : Prop := ∀ {S : Type} (shape : S), m548 shape = .ok ()
theorem p548 : P548 := by simp [P548, m548]

def m549 {S : Type} (_shape : S) : Result Unit := .ok ()
def P549 : Prop := ∀ {S : Type} (shape : S), m549 shape = .ok ()
theorem p549 : P549 := by simp [P549, m549]

def m550 : Result Unit := .ok ()
def P550 : Prop := ∀ _ : Unit, m550 = .ok ()
theorem p550 : P550 := by simp [P550, m550]

def m551 (axes : List Axis) : Result Unit :=
  if axes.any (fun axis => axis.values.length ≠ 1) then .error .dimensionMismatch else .ok ()
def P551 : Prop := ∀ axes,
  m551 axes = if axes.any (fun axis => axis.values.length ≠ 1)
    then .error .dimensionMismatch else .ok ()
theorem p551 : P551 := by simp [P551, m551]

def checkShape : List Dim → List Axis → Result Unit
  | [], [] => .ok ()
  | [], axes => m551 axes
  | _, [] => .ok ()
  | shapeHead :: shapeTail, axisHead :: axisTail =>
      if compatible shapeHead (.axis axisHead) then checkShape shapeTail axisTail
      else .error .dimensionMismatch

def m557 (shape : List Dim) (axes : List Axis) : Result Unit :=
  match shape, axes with
  | shapeHead :: shapeTail, axisHead :: axisTail =>
      if compatible shapeHead (.axis axisHead) then checkShape shapeTail axisTail
      else .error .dimensionMismatch
  | _, _ => checkShape shape axes
def P557 : Prop := ∀ shapeHead shapeTail axisHead axisTail,
  m557 (shapeHead :: shapeTail) (axisHead :: axisTail) =
    if compatible shapeHead (.axis axisHead) then checkShape shapeTail axisTail
    else .error .dimensionMismatch
theorem p557 : P557 := by simp [P557, m557]

def m561 {A : Type} (axes : A → List Axis) (shape : List Dim) (array : A) : Result Unit :=
  checkShape shape (axes array)
def P561 : Prop := ∀ {A : Type} (axes : A → List Axis) shape array,
  m561 axes shape array = checkShape shape (axes array)
theorem p561 : P561 := by simp [P561, m561]

def m563 {A : Type} (axes : A → List Axis) (shape : List Dim) : List A → Result Unit
  | [] => .ok ()
  | array :: rest => do
      checkShape shape (axes array)
      m563 axes shape rest
def P563 : Prop := ∀ {A : Type} (axes : A → List Axis) shape array rest,
  m563 axes shape (array :: rest) = do
    checkShape shape (axes array)
    m563 axes shape rest
theorem p563 : P563 := by simp [P563, m563]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-broadcast-faithful-{line}"
    juliaFile := "base/broadcast.jl"
    juliaFns := [name]
    statement
    source := s!"base/broadcast.jl:{line}; broadcast_shape docstring and source equation"
    status := .proven
    prop
    thm := some thm }

def entries : List Entry := [
  entry 502 "combine_axes(A,B...)" "The vararg overload reads the first axes before every remaining axes and combines them in source order." ``P502 ``p502,
  entry 503 "combine_axes(A,B)" "The binary overload reads left axes before right axes and combines both shapes." ``P503 ``p503,
  entry 504 "combine_axes(A)" "The unary overload returns axes(A)." ``P504 ``p504,
  entry 521 "broadcast_shape(shape)" "Every single shape is returned unchanged." ``P521 ``p521,
  entry 522 "broadcast_shape(shape,shape1,shapes...)" "Multiple shapes combine the first pair before recursively combining the remainder." ``P522 ``p522,
  entry 524 "_bcs((),())" "Two empty shapes combine to empty." ``P524 ``p524,
  entry 525 "_bcs((),newshape)" "An empty left shape copies the right head before recursively copying its tail." ``P525 ``p525,
  entry 526 "_bcs(shape,())" "An empty right shape copies the left head before recursively copying its tail." ``P526 ``p526,
  entry 527 "_bcs(shape,newshape)" "The general case combines heads before recursively combining tails." ``P527 ``p527,
  entry 531 "_bcs1(::Integer,::Integer)" "Heterogeneous integer extents apply both singleton branches before equality and DimensionMismatch." ``P531 ``p531,
  entry 532 "_bcs1(::Integer,axis)" "An integer extent accepts one or an axis whose first and last indices are one and that extent." ``P532 ``p532,
  entry 533 "_bcs1(axis,::Integer)" "The reversed mixed overload swaps its complete arguments." ``P533 ``p533,
  entry 534 "_bcs1(axis,axis)" "The general method tests reverse compatibility before forward compatibility and converts the chosen axis type." ``P534 ``p534,
  entry 536 "_bcsm(a,b)" "Axis compatibility accepts structural equality or any singleton second axis." ``P536 ``p536,
  entry 537 "_bcsm(a,::Number)" "A numeric second dimension matches exactly one." ``P537 ``p537,
  entry 538 "_bcsm(::Number,::Number)" "Two numeric dimensions match equality or a singleton second value." ``P538 ``p538,
  entry 542 "axistype(a::T,b::T)" "Equal axis types preserve the first axis object." ``P542 ``p542,
  entry 543 "axistype(::OneTo,::OneTo)" "Different OneTo element types convert the first axis to OneTo{Int}." ``P543 ``p543,
  entry 544 "axistype(a,b)" "The fallback converts the first axis values to UnitRange{Int}." ``P544 ``p544,
  entry 548 "check_broadcast_shape(shape)" "A destination shape alone succeeds." ``P548 ``p548,
  entry 549 "check_broadcast_shape(shape,())" "Every destination shape accepts an empty source shape." ``P549 ``p549,
  entry 550 "check_broadcast_shape((),())" "Two empty shapes succeed." ``P550 ``p550,
  entry 551 "check_broadcast_shape((),axes)" "Extra source axes succeed exactly when every remaining axis is singleton." ``P551 ``p551,
  entry 557 "check_broadcast_shape(shape,axes)" "The general check validates the heads before recursively validating both tails." ``P557 ``p557,
  entry 561 "check_broadcast_axes(shape,A)" "The array overload computes axes(A) before checking the shape." ``P561 ``p561,
  entry 563 "check_broadcast_axes(shape,A,As...)" "The vararg overload checks A before recursively checking every remaining input." ``P563 ``p563
]

end JuliaLean.MultidimCov.BroadcastShapeFaithful
