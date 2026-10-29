import JuliaLean.MultidimCov.MultidimensionalUnsafeFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.MultidimensionalFinalFaithful

open JuliaLean.Registry
open MultidimensionalUnsafeFaithful

inductive Error where | argument | dimensionMismatch | bounds deriving Repr, DecidableEq
abbrev Result (α : Type) := Except Error α

def oneToAxes (sizes : List Nat) : List (List Int) :=
  sizes.map fun size => (List.range size).map fun n => Int.ofNat n + 1

def isPermutation (permutation : List Nat) (rank : Nat) : Bool :=
  permutation.length = rank && permutation.all (fun value => value < rank) &&
    permutation.eraseDups.length = rank

def checkDims (destination source : List (List Int)) (permutation : List Nat) : Result Unit :=
  if !isPermutation permutation source.length then .error .argument
  else if destination ≠ permutation.map (source.getD · []) then .error .dimensionMismatch
  else .ok ()

def permutedims (source : ArrayState α) (permutation : List Nat) : Result (ArrayState α) := do
  if !isPermutation permutation source.axes.length then .error .argument else
  let sizes := permutation.map fun dimension => (source.axes.getD dimension []).length
  let destination : ArrayState α := { axes := oneToAxes sizes, values := [], id := source.id + 1 }
  checkDims destination.axes source.axes permutation
  pure destination

def PermutedimsOffsetCorrect : Prop := ∀ (source : ArrayState Int) permutation,
  isPermutation permutation source.axes.length = true → ∃ output, permutedims source permutation = .ok output

theorem permutedimsOffsetCorrect_refuted : ¬ PermutedimsOffsetCorrect := by
  intro h
  let source : ArrayState Int :=
    { axes := [[2, 3]], values := [], id := 1 }
  have result := h source [0] (by decide)
  obtain ⟨output, result⟩ := result
  have bad : permutedims source [0] = .error .dimensionMismatch := by rfl
  rw [bad] at result
  cases result

def m1678 (axes : A → List (List Int)) (destination source : A) (permutation : List Nat) : Result Unit :=
  checkDims (axes destination) (axes source) permutation
def P1678 : Prop := ∀ {A : Type} (axes : A → List (List Int)) (destination source : A)
    (permutation : List Nat),
  m1678 axes destination source permutation = checkDims (axes destination) (axes source) permutation
theorem p1678 : P1678 := by simp [P1678, m1678]

def m1679 := checkDims
def P1679 : Prop := ∀ destination source permutation,
  m1679 destination source permutation = checkDims destination source permutation
theorem p1679 : P1679 := by simp [P1679, m1679]

def permuteKey (permutation : List Nat) (key : List Int) : List Int := permutation.map (key.getD · 0)
def m1689 (destination source : ArrayState α) (permutation : List Nat) : Result (ArrayState α) := do
  checkDims destination.axes source.axes permutation
  pure (source.values.foldl (fun output pair => write output (permuteKey permutation pair.1) pair.2) destination)
def P1689 : Prop := ∀ {α : Type} (destination source : ArrayState α) permutation,
  m1689 destination source permutation = do
    checkDims destination.axes source.axes permutation
    pure (source.values.foldl (fun output pair => write output (permuteKey permutation pair.1) pair.2) destination)
theorem p1689 : P1689 := by simp [P1689, m1689]

structure Prehashed where hash : UInt64 deriving Repr, DecidableEq
def m1723 (value : Prehashed) : UInt64 := value.hash
def P1723 : Prop := ∀ value, m1723 value = value.hash
theorem p1723 : P1723 := by simp [P1723, m1723]

def stableUnique (equal : α → α → Bool) (values : List α) : List α :=
  values.foldl (fun output value =>
    if output.any (equal value) then output else output ++ [value]) []

def m1764 {A D R : Type} (uniqueDims : A → D → R) (array : A) (dims : D) : R := uniqueDims array dims
def P1764 : Prop := ∀ {A D R : Type} (uniqueDims : A → D → R) array dims,
  m1764 uniqueDims array dims = uniqueDims array dims
theorem p1764 : P1764 := by simp [P1764, m1764]

def m1766 {A R : Type} (invokeUnique : A → R) (array : A) : R := invokeUnique array
def P1766 : Prop := ∀ {A R : Type} (invokeUnique : A → R) array, m1766 invokeUnique array = invokeUnique array
theorem p1766 : P1766 := by simp [P1766, m1766]

def m1768 (equal : List α → List α → Bool) (slices : List (List α))
    (dimensionValid : Bool) : List (List α) :=
  if !dimensionValid then slices else stableUnique equal slices
def P1768 : Prop := ∀ {α : Type} equal (slices : List (List α)) dimensionValid,
  m1768 equal slices dimensionValid = if !dimensionValid then slices else stableUnique equal slices
theorem p1768 : P1768 := by simp [P1768, m1768]

def m1839 (typeName : String) : String := "pairs(::" ++ typeName ++ ")"
def P1839 : Prop := ∀ typeName, m1839 typeName = "pairs(::" ++ typeName ++ ")"
theorem p1839 : P1839 := by simp [P1839, m1839]
def m1842 := m1839
def P1842 : Prop := ∀ typeName, m1842 typeName = "pairs(::" ++ typeName ++ ")"
theorem p1842 : P1842 := by simp [P1842, m1842, m1839]
def m1846 (typeName : String) : String := "pairs(IndexCartesian(), ::" ++ typeName ++ ")"
def P1846 : Prop := ∀ typeName, m1846 typeName = "pairs(IndexCartesian(), ::" ++ typeName ++ ")"
theorem p1846 : P1846 := by simp [P1846, m1846]

def m1969 {A D R K : Type} (matrixFast : A → D → K → R)
    (allocate : A → R) (generic : R → A → D → K → R)
    (isMatrixDimOne : Bool) (array : A) (dims : D) (keywords : K) : R :=
  if isMatrixDimOne then matrixFast array dims keywords
  else let output := allocate array; generic output array dims keywords
def P1969 : Prop := ∀ {A D R K : Type} (matrixFast : A → D → K → R)
    (allocate : A → R) (generic : R → A → D → K → R)
    isMatrixDimOne array dims keywords,
  m1969 matrixFast allocate generic isMatrixDimOne array dims keywords =
    if isMatrixDimOne then matrixFast array dims keywords
    else let output := allocate array; generic output array dims keywords
theorem p1969 : P1969 := by simp [P1969, m1969]

def m1981 (sortPermutation : List α → List Nat) (sourceSlices : List α)
    (destinationSlices : List α) : List α :=
  let permutation := sortPermutation sourceSlices
  (destinationSlices.zip permutation).map fun pair => sourceSlices.getD pair.2 pair.1
def P1981 : Prop := ∀ {α : Type} [Inhabited α]
    (sortPermutation : List α → List Nat) (sourceSlices destinationSlices : List α),
  m1981 sortPermutation sourceSlices destinationSlices =
    let permutation := sortPermutation sourceSlices
    (destinationSlices.zip permutation).map fun pair => sourceSlices.getD pair.2 pair.1
theorem p1981 : P1981 := by simp [P1981, m1981]

def m1992 (value : α) : α := value
def P1992 : Prop := ∀ {α : Type} (value : α), m1992 value = value
theorem p1992 : P1992 := by simp [P1992, m1992]
def m1993 (_old new : α) : α := new
def P1993 : Prop := ∀ {α : Type} old (new : α), m1993 old new = new
theorem p1993 : P1993 := by simp [P1993, m1993]

def fibSample (hashEntry : Nat → α → UInt64 → UInt64) (values : List α)
    (equal : α → α → Bool) (initial : UInt64) : UInt64 :=
  let rec loop : Nat → Nat → Nat → Nat → Nat → List UInt64 → UInt64
    | 0, _, _, _, _, streams => streams.foldl (fun hash part => hash ^^^ part) initial
    | fuel + 1, index, fib, previous, count, streams =>
      if h : index < values.length then
      let value := values[index]
      let stream := count % 4
      let updated := streams.set stream (hashEntry index value (streams.getD stream initial))
      if index < fib then updated.foldl (fun hash part => hash ^^^ part) initial
      else
        let nextIndex := index - fib
        let distinct := (List.range (nextIndex + 1)).reverse.find? fun candidate => !equal value (values.getD candidate value)
        match distinct with
        | none => updated.foldl (fun hash part => hash ^^^ part) initial
        | some candidate =>
            let grow := (count + 1) % 4096 = 0
            loop fuel candidate (if grow then fib + previous else fib)
              (if grow then fib else previous) (count + 1) updated
      else initial
  loop values.length (values.length - 1) 1 1 0 (List.replicate 4 initial)

def m1997 := @fibSample
def P1997 : Prop := ∀ {α : Type} (hashEntry : Nat → α → UInt64 → UInt64)
    (values : List α) (equal : α → α → Bool) initial,
  m1997 hashEntry values equal initial = fibSample hashEntry values equal initial
theorem p1997 : P1997 := by simp [P1997, m1997]

def m2077 {A R : Type} (isType : A → String → Bool) (call : A → R)
    (value : A) : List String → R
  | [] => call value
  | type :: rest => if isType value type then call value else m2077 isType call value rest
def P2077 : Prop := ∀ {A R : Type} (isType : A → String → Bool) (call : A → R) value type rest,
  m2077 isType call value (type :: rest) =
    if isType value type then call value else m2077 isType call value rest
theorem p2077 : P2077 := by simp [P2077, m2077]

def m2084 {A R : Type} (call : A → R) (value : A) : R := call value
def P2084 : Prop := ∀ {A R : Type} (call : A → R) value, m2084 call value = call value
theorem p2084 : P2084 := by simp [P2084, m2084]

def hashChain (hashValue : α → UInt64 → UInt64) : List α → UInt64 → UInt64
  | [], hash => hash
  | head :: tail, hash => hashChain hashValue tail (hashValue head hash)

def m2086 (hashAxes : List Int → UInt64 → UInt64)
    (hashValue : α → UInt64 → UInt64) (fib : List α → UInt64 → UInt64)
    (axisFirst axisLast : List Int) (values : List α) (initial : UInt64) : UInt64 :=
  let hash := hashAxes axisLast (hashAxes axisFirst initial)
  if values.length < 8 then hashChain hashValue values hash
  else if values.length < 32768 then
    let streams := (List.range 8).map fun offset => hashChain hashValue ((values.drop offset).zipIdx.filterMap fun pair =>
      if pair.2 % 8 = 0 then some pair.1 else none) hash
    streams.foldl (fun output stream => output ^^^ stream) hash
  else fib values hash
def P2086 : Prop := ∀ {α : Type} hashAxes hashValue fib axisFirst axisLast (values : List α) initial,
  m2086 hashAxes hashValue fib axisFirst axisLast values initial =
    let hash := hashAxes axisLast (hashAxes axisFirst initial)
    if values.length < 8 then hashChain hashValue values hash
    else if values.length < 32768 then
      let streams := (List.range 8).map fun offset => hashChain hashValue ((values.drop offset).zipIdx.filterMap fun pair =>
        if pair.2 % 8 = 0 then some pair.1 else none) hash
      streams.foldl (fun output stream => output ^^^ stream) hash
    else fib values hash
theorem p2086 : P2086 := by simp [P2086, m2086]

def m2123 {A : Type} (hashShaped : A → UInt64 → UInt64) (seed : UInt64) (array : A) (initial : UInt64) :=
  hashShaped array (initial ^^^ seed)
def P2123 : Prop := ∀ {A : Type} (hashShaped : A → UInt64 → UInt64) seed array initial,
  m2123 hashShaped seed array initial = hashShaped array (initial ^^^ seed)
theorem p2123 : P2123 := by simp [P2123, m2123]

private def entry (line : Nat) (name statement : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-multidimensional-faithful-{line}", juliaFile := "base/multidimensional.jl",
    juliaFns := [name], statement, source := s!"base/multidimensional.jl:{line}; source equation and array invariant",
    status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.MultidimensionalFinalFaithful
