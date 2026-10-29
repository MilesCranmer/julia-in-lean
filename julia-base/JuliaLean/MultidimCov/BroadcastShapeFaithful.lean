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
  first : Int
  last : Int
  length : Nat
  deriving Repr, DecidableEq

inductive Dim where
  | integer (value : Integer)
  | axis (value : Axis)
  deriving Repr, DecidableEq

def axisFirst (axis : Axis) : Int := axis.first
def axisLast (axis : Axis) : Int := axis.last
def dimLength : Dim → Nat
  | .integer value => if value.value < 0 then 0 else value.value.toNat
  | .axis axis => axis.length

def compatible (a b : Dim) : Bool := a = b || dimLength b = 1

def axisType (a b : Axis) : Axis :=
  if a.kind = b.kind then a
  else match a.kind, b.kind with
    | .oneTo _, .oneTo _ => { a with kind := .oneTo "Int" }
    | _, _ => { a with kind := .unitRange "Int" }

def bcs1 : Dim → Dim → Result Dim
  | .integer a, .integer b =>
      if a.value = 1 then .ok (.integer b)
      else if b.value = 1 then .ok (.integer a)
      else if a.value = b.value then .ok (.integer a)
      else .error .dimensionMismatch
  | .integer a, .axis b =>
      if a.value = 1 then .ok (.axis b)
      else if axisFirst b = 1 && axisLast b = a.value then .ok (.axis b)
      else .error .dimensionMismatch
  | .axis a, .integer b =>
      if b.value = 1 then .ok (.axis a)
      else if axisFirst a = 1 && axisLast a = b.value then .ok (.axis a)
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

def combineAxes (axes : A → Result (List Dim))
    (combine : List Dim → List Dim → Result (List Dim)) : A → List A → Result (List Dim)
  | first, [] => axes first
  | first, next :: rest => do
      let firstAxes ← axes first
      let tailAxes ← combineAxes axes combine next rest
      combine firstAxes tailAxes

def m502 {A : Type} (axes : A → Result (List Dim))
    (combine : List Dim → List Dim → Result (List Dim))
    (first next : A) (rest : List A) : Result (List Dim) :=
  combineAxes axes combine first (next :: rest)
def P502 : Prop := ∀ {A : Type} (axes : A → Result (List Dim)) combine first next rest,
  m502 axes combine first next rest = do
    let firstAxes ← axes first
    let tailAxes ← combineAxes axes combine next rest
    combine firstAxes tailAxes
theorem p502 : P502 := by simp [P502, m502, combineAxes]

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
  if a.value = 1 then .ok b
  else if axisFirst b = 1 && axisLast b = a.value then .ok b
  else .error .dimensionMismatch
def P532 : Prop := ∀ a b,
  m532 a b =
    if a.value = 1 then .ok b
    else if axisFirst b = 1 && axisLast b = a.value then .ok b
    else .error .dimensionMismatch
theorem p532 : P532 := by
  intro a b
  by_cases ha : a.value = 1
  · simp [m532, ha]
  · by_cases haxis : axisFirst b = 1 && axisLast b = a.value
    · simp [m532, ha, haxis]
    · simp [m532, ha, haxis]

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

def m536 (a b : Axis) : Bool := a = b || b.length = 1
def P536 : Prop := ∀ a b, m536 a b = (a = b || b.length = 1)
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

def m543 (oneToInt : Axis → Result Axis) (a : Axis) (_b : Axis) : Result Axis :=
  oneToInt a
def P543 : Prop := ∀ oneToInt a b, m543 oneToInt a b = oneToInt a
theorem p543 : P543 := by simp [P543, m543]

def m544 (unitRangeInt : Axis → Result Axis) (a : Axis) (_b : Axis) : Result Axis :=
  unitRangeInt a
def P544 : Prop := ∀ unitRangeInt a b, m544 unitRangeInt a b = unitRangeInt a
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
  if axes.any (fun axis => axis.length ≠ 1) then .error .dimensionMismatch else .ok ()
def P551 : Prop := ∀ axes,
  m551 axes = if axes.any (fun axis => axis.length ≠ 1)
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

def entries : List Entry := []

end JuliaLean.MultidimCov.BroadcastShapeFaithful
