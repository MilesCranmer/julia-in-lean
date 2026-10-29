import JuliaLean.MultidimCov.LogicalFaithfulCore
import JuliaLean.MultidimCov.MultidimensionalDispatchFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalLogicalFaithful

open JuliaLean.Registry
open MultidimensionalCartesianFaithful
open MultidimensionalIndicesFaithful
open MultidimensionalIteratorFaithful
open MultidimensionalDispatchFaithful
open LogicalFaithfulCore

abbrev Result (α : Type) := Except Error α
abbrev CIAxis := MultidimensionalCartesianFaithful.Axis
abbrev MaskAxis := JuliaLean.MultidimCov.Axis

def m837 (kind : IndexKind) (mask : Mask) : LogicalIndex := construct kind mask
def P837 : Prop := ∀ kind mask,
  m837 kind mask = { mask, cachedCount := mask.values.count true, kind }
theorem p837 : P837 := by simp [P837, m837, construct]

def m839 (mask : Mask) : LogicalIndex := construct .linear mask
def P839 : Prop := ∀ mask, m839 mask = construct .linear mask
theorem p839 : P839 := by simp [P839, m839]

def m840 (rank : Nat) (mask : Mask) : LogicalIndex := construct (.cartesian rank) mask
def P840 : Prop := ∀ rank mask, m840 rank mask = construct (.cartesian rank) mask
theorem p840 : P840 := by simp [P840, m840]

def m841 (mask : Mask) : LogicalIndex := construct .linear mask
def P841 : Prop := ∀ mask, m841 mask = construct .linear mask
theorem p841 : P841 := by simp [P841, m841]

def m844 {R : Type} (print : List Output → R) (initial : R → R) (index : LogicalIndex) : R :=
  initial (print (collect index))
def P844 : Prop := ∀ {R : Type} (print : List Output → R) (initial : R → R) index,
  m844 print initial index = initial (print (collect index))
theorem p844 : P844 := by simp [P844, m844]

def m845 {R : Type} (printArray : List Output → R) (index : LogicalIndex) : R := printArray (collect index)
def P845 : Prop := ∀ {R : Type} (printArray : List Output → R) index,
  m845 printArray index = printArray (collect index)
theorem p845 : P845 := by simp [P845, m845]

structure LogicalState where
  count : Nat
  position : Nat
  deriving Repr, DecidableEq

def nextTrue (index : LogicalIndex) (state : LogicalState) : Option (Output × LogicalState) :=
  if state.count > index.cachedCount then none else
  match ((index.mask.values.drop state.position).findIdx? id) with
  | none => none
  | some relative =>
      let position := state.position + relative
      some (outputAt index position, { count := state.count + 1, position := position + 1 })

def m851 (index : LogicalIndex) : Option (Output × LogicalState) :=
  nextTrue index { count := 1, position := 0 }
def P851 : Prop := ∀ index, m851 index = nextTrue index { count := 1, position := 0 }
theorem p851 : P851 := by simp [P851, m851]
def m855 := m851
def P855 : Prop := ∀ index, m855 index = nextTrue index { count := 1, position := 0 }
theorem p855 : P855 := by simp [P855, m855, m851]

def m859 (index : LogicalIndex) (state : LogicalState) := nextTrue index state
def P859 : Prop := ∀ index state, m859 index state = nextTrue index state
theorem p859 : P859 := by simp [P859, m859]

def chunksToMask : List UInt64 → Nat → List Bool
  | _, 0 => []
  | [], n => List.replicate n false
  | chunk :: chunks, n =>
      (List.range (min 64 n)).map (fun (bit : Nat) =>
        decide ((chunk &&& ((1 : UInt64) <<< UInt64.ofNat bit)) ≠ 0)) ++
        chunksToMask chunks (n - 64)

def m874 (index : LogicalIndex) (chunks : List UInt64) : Option (Output × LogicalState) :=
  if index.cachedCount = 0 then none else
  nextTrue { index with mask := { index.mask with values := chunksToMask chunks index.mask.values.length } }
    { count := 1, position := 0 }
def P874 : Prop := ∀ index chunks, m874 index chunks =
  if index.cachedCount = 0 then none else
  nextTrue { index with mask := { index.mask with values := chunksToMask chunks index.mask.values.length } }
    { count := 1, position := 0 }
theorem p874 : P874 := by simp [P874, m874]

def m879 (index : LogicalIndex) (chunks : List UInt64) : Option (Output × LogicalState) := m874 index chunks
def P879 : Prop := ∀ index chunks, m879 index chunks = m874 index chunks
theorem p879 : P879 := by simp [P879, m879]

def m885 (index : LogicalIndex) (chunks : List UInt64) (state : LogicalState) : Option (Output × LogicalState) :=
  nextTrue { index with mask := { index.mask with values := chunksToMask chunks index.mask.values.length } } state
def P885 : Prop := ∀ index chunks state, m885 index chunks state =
  nextTrue { index with mask := { index.mask with values := chunksToMask chunks index.mask.values.length } } state
theorem p885 : P885 := by simp [P885, m885]

def m900 {A : Type} (checkbounds : A → Mask → Bool) (array : A) (index : LogicalIndex) : Bool :=
  checkbounds array index.mask
def P900 : Prop := ∀ {A : Type} (checkbounds : A → Mask → Bool) array index,
  m900 checkbounds array index = checkbounds array index.mask
theorem p900 : P900 := by simp [P900, m900]

def m902 {R : Type} (checkindex : R → Mask → Bool) (range : R) (index : LogicalIndex) : Bool :=
  checkindex range index.mask
def P902 : Prop := ∀ {R : Type} (checkindex : R → Mask → Bool) range index,
  m902 checkindex range index = checkindex range index.mask
theorem p902 : P902 := by simp [P902, m902]

def m903 (checkindex : List CIAxis → Mask → Bool) (axes : List CIAxis) (index : LogicalIndex) : Bool :=
  checkindex axes index.mask
def P903 : Prop := ∀ checkindex axes index, m903 checkindex axes index = checkindex axes index.mask
theorem p903 : P903 := by simp [P903, m903]

def m907 {A : Type} (axes : A → List CIAxis) (check : List CIAxis → Mask → Bool)
    (array : A) (mask : Mask) : Bool := check (axes array) mask
def P907 : Prop := ∀ {A : Type} (axes : A → List CIAxis) check array mask,
  m907 axes check array mask = check (axes array) mask
theorem p907 : P907 := by simp [P907, m907]

def m910 {A : Type} (linearIndices : A → CIAxis) (check : CIAxis → Mask → Bool)
    (array : A) (mask : Mask) : Bool := check (linearIndices array) mask
def P910 : Prop := ∀ {A : Type} (linearIndices : A → CIAxis) check array mask,
  m910 linearIndices check array mask = check (linearIndices array) mask
theorem p910 : P910 := by simp [P910, m910]

def m912 (rank : Nat) (checkHead : List CIAxis → Mask → Bool)
    (recursive : List CIAxis → List Mask → Bool) (axes : List CIAxis) (head : Mask) (tail : List Mask) : Bool :=
  let split := splitList axes rank
  checkHead split.1 head && recursive split.2 tail
def P912 : Prop := ∀ rank checkHead recursive axes head tail,
  m912 rank checkHead recursive axes head tail =
    let split := splitList axes rank
    checkHead split.1 head && recursive split.2 tail
theorem p912 : P912 := by simp [P912, m912]

def m916 (axis : MaskAxis) (mask : Mask) : Bool := mask.axes.head? = some axis
def P916 : Prop := ∀ (axis : MaskAxis) mask, m916 axis mask = (mask.axes.head? = some axis)
theorem p916 : P916 := by simp [P916, m916]
def m917 := m916
def P917 : Prop := ∀ (axis : MaskAxis) mask, m917 axis mask = (mask.axes.head? = some axis)
theorem p917 : P917 := by simp [P917, m917, m916]

def checkBooleanAxes : List MaskAxis → List MaskAxis → Bool
  | [], rest => rest.all fun axis => axis.first.val = 1 && axis.len = 1
  | _, [] => false
  | head :: tail, axis :: axes => head = axis && checkBooleanAxes tail axes
def m918 (axes : List MaskAxis) (mask : Mask) : Bool := checkBooleanAxes axes mask.axes
def P918 : Prop := ∀ axes mask, m918 axes mask = checkBooleanAxes axes mask.axes
theorem p918 : P918 := by simp [P918, m918]

inductive Ensured (α : Type) where
  | value (value : α)
  | logical (values : List Output)
  deriving Repr, DecidableEq
def m924 (head : LogicalIndex) (tail : List (Ensured α)) : List (Ensured α) :=
  .logical (collect head) :: tail
def P924 : Prop := ∀ {α : Type} head (tail : List (Ensured α)),
  m924 head tail = .logical (collect head) :: tail
theorem p924 : P924 := by simp [P924, m924]

def m928 {A R : Type} (toIndices : A → List CIAxis → List IntegerValue → R)
    (array : A) (indices : List IntegerValue) : R := toIndices array [] indices
def P928 : Prop := ∀ {A R : Type} (toIndices : A → List CIAxis → List IntegerValue → R) array indices,
  m928 toIndices array indices = toIndices array [] indices
theorem p928 : P928 := by simp [P928, m928]

def m932 {A I T : Type} (toIndex : A → I64 → Result I)
    (recursive : A → List CIAxis → T → Result (List I)) (array : A) (axes : List CIAxis)
    (head : Cartesian) (tail : T) : Result (List I) := do
  let split := splitList axes head.coordinates.length
  let converted ← head.coordinates.mapM (toIndex array)
  pure (converted ++ (← recursive array split.2 tail))
def P932 : Prop := ∀ {A I T : Type} (toIndex : A → I64 → Result I)
    (recursive : A → List CIAxis → T → Result (List I)) array axes head tail,
  m932 toIndex recursive array axes head tail = do
    let split := splitList axes head.coordinates.length
    let converted ← head.coordinates.mapM (toIndex array)
    pure (converted ++ (← recursive array split.2 tail))
theorem p932 : P932 := by simp [P932, m932]

def m937 {A I T : Type} (toIndex : A → T → Result I)
    (recursive : A → List CIAxis → List T → Result (List I)) (array : A) (axes : List CIAxis)
    (rank : Nat) (head : T) (tail : List T) : Result (List I) := do
  let split := splitList axes rank
  pure ((← toIndex array head) :: (← recursive array split.2 tail))
def P937 : Prop := ∀ {A I T : Type} (toIndex : A → T → Result I)
    (recursive : A → List CIAxis → List T → Result (List I)) array axes rank head tail,
  m937 toIndex recursive array axes rank head tail = do
    let split := splitList axes rank
    pure ((← toIndex array head) :: (← recursive array split.2 tail))
theorem p937 : P937 := by simp [P937, m937]

def m942 := @m937
def P942 : Prop := ∀ {A I T : Type} (toIndex : A → T → Result I)
    (recursive : A → List CIAxis → List T → Result (List I)) array axes rank head tail,
  m942 toIndex recursive array axes rank head tail = m937 toIndex recursive array axes rank head tail
theorem p942 : P942 := by simp [P942, m942]

def m947 {A I : Type} (style : A → IndexStyle)
    (general : A → Mask → I) (linear : Mask → I) (array : A) (mask : Mask) : I :=
  match style array with | .linear => linear mask | .cartesian => general array mask
def P947 : Prop := ∀ {A I : Type} (style : A → IndexStyle)
    (general : A → Mask → I) (linear : Mask → I) array mask,
  m947 style general linear array mask = match style array with
    | .linear => linear mask | .cartesian => general array mask
theorem p947 : P947 := by simp [P947, m947]

def m948 {A I : Type} (toIndex : A → I → I) (array : A) (index : I) := toIndex array index
def P948 : Prop := ∀ {A I : Type} (toIndex : A → I → I) array index, m948 toIndex array index = toIndex array index
theorem p948 : P948 := by simp [P948, m948]
def m949 (mask : Mask) : LogicalIndex := construct .linear mask
def P949 : Prop := ∀ mask, m949 mask = construct .linear mask
theorem p949 : P949 := by simp [P949, m949]

inductive Slice where | slice (axis : CIAxis) deriving Repr, DecidableEq
def m952 {A I T : Type} (recursive : A → List CIAxis → T → Result (List I))
    (convertSlice : CIAxis → I) (array : A) (axes : List CIAxis) (tail : T) : Result (List I) :=
  match axes with
  | [] => do pure (convertSlice ⟨JInt.lit .i64 1, JInt.lit .i64 1, JInt.lit .i64 1⟩ :: (← recursive array [] tail))
  | axis :: rest => do pure (convertSlice axis :: (← recursive array rest tail))
def P952 : Prop := ∀ {A I T : Type} (recursive : A → List CIAxis → T → Result (List I))
    (convertSlice : CIAxis → I) (array : A) axes (tail : T),
  m952 recursive convertSlice array axes tail = match axes with
    | [] => do pure (convertSlice ⟨JInt.lit .i64 1, JInt.lit .i64 1, JInt.lit .i64 1⟩ :: (← recursive array [] tail))
    | axis :: rest => do pure (convertSlice axis :: (← recursive array rest tail))
theorem p952 : P952 := by simp [P952, m952]

def m955 : Slice := .slice ⟨JInt.lit .i64 1, JInt.lit .i64 1, JInt.lit .i64 1⟩
def P955 : Prop := ∀ _ : Unit, m955 = .slice ⟨JInt.lit .i64 1, JInt.lit .i64 1, JInt.lit .i64 1⟩
theorem p955 : P955 := by simp [P955, m955]
def m956 (axis : CIAxis) : Slice := .slice axis
def P956 : Prop := ∀ axis, m956 axis = .slice axis
theorem p956 : P956 := by simp [P956, m956]

def m964 {I S R : Type} (iterate : I → Option (R × S)) (iter : I) := iterate iter
def P964 : Prop := ∀ {I S R : Type} (iterate : I → Option (R × S)) iter, m964 iterate iter = iterate iter
theorem p964 : P964 := by simp [P964, m964]
def m965 {I S R : Type} (iterate : I → S → Option (R × S)) (iter : I) (state : S) := iterate iter state
def P965 : Prop := ∀ {I S R : Type} (iterate : I → S → Option (R × S)) iter state, m965 iterate iter state = iterate iter state
theorem p965 : P965 := by simp [P965, m965]
def m967 (first : I64) : I64 × I64 := (first, first)
def P967 : Prop := ∀ first, m967 first = (first, first)
theorem p967 : P967 := by simp [P967, m967]
def m968 (convert : Int → Result I64) (state step : Int) : Result (I64 × I64) := do
  let next ← convert (state + step); pure (next, next)
def P968 : Prop := ∀ convert state step, m968 convert state step = do
  let next ← convert (state + step); pure (next, next)
theorem p968 : P968 := by simp [P968, m968]
def m978 (state : Cartesian) (axes : List CIAxis) : Cartesian × Cartesian :=
  let next : Cartesian := ⟨inc state.coordinates axes⟩
  (next, next)
def P978 : Prop := ∀ state axes, m978 state axes =
  let next : Cartesian := ⟨inc state.coordinates axes⟩; (next, next)
theorem p978 : P978 := by simp [P978, m978]
def m982 {I : Type} (first : I) : I × I := (first, first)
def P982 : Prop := ∀ {I : Type} (first : I), m982 first = (first, first)
theorem p982 : P982 := by simp [P982, m982]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; LogicalIndex and conversion source equation",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalLogicalFaithful
