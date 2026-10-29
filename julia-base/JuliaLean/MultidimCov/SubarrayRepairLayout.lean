import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayRepairLayout

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

variable {I X R D J P S AX O IP LI F K IH IF AH AF L V A : Type}

/-! Source-order models replacing the remaining HOLLOW layout and axis rows in
`base/subarray.jl:443-534`. -/

def m443 (head : I → X) (typeOf : X → AnyValue) (indices : I) : JResult R :=
  .error (.argument (lazyAppend [
    .literal "strides is invalid for SubArrays with indices of type ",
    .dynamic (typeOf (head indices))]))

def P443 : Prop := ∀ (head : I → X) (typeOf : X → AnyValue) indices,
  m443 (R := R) head typeOf indices = (.error (.argument (lazyAppend [
    .literal "strides is invalid for SubArrays with indices of type ",
    .dynamic (typeOf (head indices))])) : JResult R)

theorem p443 {I X R : Type} : P443 (I := I) (X := X) (R := R) := by unfold P443; intros; rfl

def m478 (findDims : Nat → I → JResult D) (findIndices : I → JResult J)
    (computeOffset : P → S → D → J → I → JResult R)
    (parent : P) (stride : S) (indices : I) : JResult R := do
  let dims ← findDims 1 indices
  let extended ← findIndices indices
  computeOffset parent stride dims extended indices

def P478 : Prop := ∀ (findDims : Nat → I → JResult D) (findIndices : I → JResult J)
    (computeOffset : P → S → D → J → I → JResult R) parent stride indices,
  m478 findDims findIndices computeOffset parent stride indices = do
    let dims ← findDims 1 indices
    let extended ← findIndices indices
    computeOffset parent stride dims extended indices

theorem p478 {I D J P S R : Type} :
    P478 (I := I) (D := D) (J := J) (P := P) (S := S) (R := R) := by
  unfold P478
  intros
  rfl

def m486 (axes : P → JResult AX) (oneToOne : O)
    (fillToLength : AX → O → Nat → JResult IP) (linearIndices : P → JResult LI)
    (first : LI → JResult F) (toInt : F → JResult K)
    (compute : K → K → IP → I → JResult R) (one : K)
    (parent : P) (rank : Nat) (indices : I) : JResult R := do
  let parentAxes ← axes parent
  let filled ← fillToLength parentAxes oneToOne rank
  let linear ← linearIndices parent
  let firstLinear ← first linear
  let start ← toInt firstLinear
  compute start one filled indices

def P486 : Prop := ∀ (axes : P → JResult AX) (oneToOne : O)
    (fillToLength : AX → O → Nat → JResult IP) (linearIndices : P → JResult LI)
    (first : LI → JResult F) (toInt : F → JResult K)
    (compute : K → K → IP → I → JResult R) one parent rank indices,
  m486 axes oneToOne fillToLength linearIndices first toInt compute one parent rank indices = do
    let parentAxes ← axes parent
    let filled ← fillToLength parentAxes oneToOne rank
    let linear ← linearIndices parent
    let firstLinear ← first linear
    let start ← toInt firstLinear
    compute start one filled indices

theorem p486 {P AX O IP LI F K I R : Type} :
    P486 (P := P) (AX := AX) (O := O) (IP := IP) (LI := LI) (F := F)
      (K := K) (I := I) (R := R) := by
  unfold P486
  intros
  rfl

def m491
    (headI : I → JResult IH) (firstI : IH → JResult IF) (toIntI : IF → JResult K)
    (headIP : IP → JResult AH) (firstIP : AH → JResult AF) (toIntIP : AF → JResult K)
    (subtract : K → K → JResult K) (multiply : K → K → JResult K)
    (add : K → K → JResult K) (length : AH → JResult L) (toIntLength : L → JResult K)
    (tailIP : IP → JResult IP) (tailI : I → JResult I)
    (compute : K → K → IP → I → JResult R)
    (f s : K) (parentIndices : IP) (indices : I) : JResult R := do
  let indexHead ← headI indices
  let indexFirst ← firstI indexHead
  let indexValue ← toIntI indexFirst
  let parentHead ← headIP parentIndices
  let parentFirst ← firstIP parentHead
  let parentValue ← toIntIP parentFirst
  let delta ← subtract indexValue parentValue
  let scaledDelta ← multiply delta s
  let nextF ← add f scaledDelta
  let parentLength ← length parentHead
  let parentLengthInt ← toIntLength parentLength
  let nextS ← multiply s parentLengthInt
  let remainingParent ← tailIP parentIndices
  let remainingIndices ← tailI indices
  compute nextF nextS remainingParent remainingIndices

def P491 : Prop := ∀
    (headI : I → JResult IH) (firstI : IH → JResult IF) (toIntI : IF → JResult K)
    (headIP : IP → JResult AH) (firstIP : AH → JResult AF) (toIntIP : AF → JResult K)
    (subtract : K → K → JResult K) (multiply : K → K → JResult K)
    (add : K → K → JResult K) (length : AH → JResult L) (toIntLength : L → JResult K)
    (tailIP : IP → JResult IP) (tailI : I → JResult I)
    (compute : K → K → IP → I → JResult R) f s parentIndices indices,
  m491 headI firstI toIntI headIP firstIP toIntIP subtract multiply add length
      toIntLength tailIP tailI compute f s parentIndices indices = do
    let indexHead ← headI indices
    let indexFirst ← firstI indexHead
    let indexValue ← toIntI indexFirst
    let parentHead ← headIP parentIndices
    let parentFirst ← firstIP parentHead
    let parentValue ← toIntIP parentFirst
    let delta ← subtract indexValue parentValue
    let scaledDelta ← multiply delta s
    let nextF ← add f scaledDelta
    let parentLength ← length parentHead
    let parentLengthInt ← toIntLength parentLength
    let nextS ← multiply s parentLengthInt
    let remainingParent ← tailIP parentIndices
    let remainingIndices ← tailI indices
    compute nextF nextS remainingParent remainingIndices

theorem p491 {I IH IF K IP AH AF L R : Type} :
    P491 (I := I) (IH := IH) (IF := IF) (K := K) (IP := IP) (AH := AH)
      (AF := AF) (L := L) (R := R) := by
  unfold P491
  intros
  rfl

def m496
    (headI : I → JResult IH) (firstI : IH → JResult IF) (toIntI : IF → JResult K)
    (headIP : IP → JResult AH) (firstIP : AH → JResult AF) (toIntIP : AF → JResult K)
    (subtract : K → K → JResult K) (multiply : K → K → JResult K)
    (add : K → K → JResult K) (f s : K) (parentIndices : IP) (indices : I) : JResult K := do
  let indexHead ← headI indices
  let indexFirst ← firstI indexHead
  let indexValue ← toIntI indexFirst
  let parentHead ← headIP parentIndices
  let parentFirst ← firstIP parentHead
  let parentValue ← toIntIP parentFirst
  let delta ← subtract indexValue parentValue
  let scaledDelta ← multiply delta s
  add f scaledDelta

def P496 : Prop := ∀
    (headI : I → JResult IH) (firstI : IH → JResult IF) (toIntI : IF → JResult K)
    (headIP : IP → JResult AH) (firstIP : AH → JResult AF) (toIntIP : AF → JResult K)
    (subtract : K → K → JResult K) (multiply : K → K → JResult K)
    (add : K → K → JResult K) f s parentIndices indices,
  m496 headI firstI toIntI headIP firstIP toIntIP subtract multiply add
      f s parentIndices indices = do
    let indexHead ← headI indices
    let indexFirst ← firstI indexHead
    let indexValue ← toIntI indexFirst
    let parentHead ← headIP parentIndices
    let parentFirst ← firstIP parentHead
    let parentValue ← toIntIP parentFirst
    let delta ← subtract indexValue parentValue
    let scaledDelta ← multiply delta s
    add f scaledDelta

theorem p496 {I IH IF K IP AH AF : Type} :
    P496 (I := I) (IH := IH) (IF := IF) (K := K) (IP := IP) (AH := AH)
      (AF := AF) := by
  unfold P496
  intros
  rfl

def m510 (parent : V → P) (offset : V → K) (stride : V → K)
    (multiply : K → I → K) (add : K → K → K) (pointer : P → K → JResult R)
    (view : V) (index : I) : JResult R :=
  pointer (parent view) (add (offset view) (multiply (stride view) index))

def P510 : Prop := ∀ (parent : V → P) (offset : V → K) (stride : V → K)
    (multiply : K → I → K) (add : K → K → K) (pointer : P → K → JResult R)
    view index,
  m510 parent offset stride multiply add pointer view index =
    pointer (parent view) (add (offset view) (multiply (stride view) index))

theorem p510 {V P K I R : Type} :
    P510 (V := V) (P := P) (K := K) (I := I) (R := R) := by unfold P510; intros; rfl

def m511 (parent : V → P) (offset : V → K) (add : K → I → K)
    (pointer : P → K → JResult R) (view : V) (index : I) : JResult R :=
  pointer (parent view) (add (offset view) index)

def P511 : Prop := ∀ (parent : V → P) (offset : V → K) (add : K → I → K)
    (pointer : P → K → JResult R) view index,
  m511 parent offset add pointer view index = pointer (parent view) (add (offset view) index)

theorem p511 {V P K I R : Type} :
    P511 (V := V) (P := P) (K := K) (I := I) (R := R) := by unfold P511; intros; rfl

inductive IndexKind where
  | scalar
  | array
  deriving Repr, DecidableEq

def indicesSub (kind : I → IndexKind) (axes : I → JResult (List A)) : List I → JResult (List A)
  | [] => .ok []
  | head :: tail => match kind head with
    | .scalar => indicesSub kind axes tail
    | .array => do
        let firstAxes ← axes head
        let rest ← indicesSub kind axes tail
        pure (firstAxes ++ rest)

def m525 (indices : V → List I) (kind : I → IndexKind)
    (axes : I → JResult (List A)) (view : V) : JResult (List A) :=
  indicesSub kind axes (indices view)

def P525 : Prop := ∀ (indices : V → List I) (kind : I → IndexKind)
    (axes : I → JResult (List A)) view,
  m525 indices kind axes view = indicesSub kind axes (indices view)

theorem p525 {V I A : Type} :
    P525 (V := V) (I := I) (A := A) := by unfold P525; intros; rfl

inductive Axis1Kind where
  | scalar
  | zeroDimensional
  | array
  deriving Repr, DecidableEq

inductive Axis1Result (A : Type) where
  | empty
  | axis (value : A)
  deriving Repr, DecidableEq

def axes1Sub (kind : I → Axis1Kind) (axes1 : I → JResult A) : List I → JResult (Axis1Result A)
  | [] => .ok .empty
  | head :: tail => match kind head with
    | .scalar => axes1Sub kind axes1 tail
    | .zeroDimensional => axes1Sub kind axes1 tail
    | .array => do pure (.axis (← axes1 head))

def m534 (indices : V → List I) (kind : I → Axis1Kind)
    (axes1 : I → JResult A) (view : V) : JResult (Axis1Result A) :=
  axes1Sub kind axes1 (indices view)

def P534 : Prop := ∀ (indices : V → List I) (kind : I → Axis1Kind)
    (axes1 : I → JResult A) view,
  m534 indices kind axes1 view = axes1Sub kind axes1 (indices view)

theorem p534 {V I A : Type} :
    P534 (V := V) (I := I) (A := A) := by unfold P534; intros; rfl


/-! Closed forms of the properties above, quantified over every choice of the
model's carrier types, so each registry `prop` is a closed `Prop`. -/

def P443All : Prop := ∀ {I X R : Type}, P443 (I := I) (X := X) (R := R)
theorem p443All : P443All := by intros; exact p443

def P478All : Prop := ∀ {I D J P S R : Type}, P478 (I := I) (D := D) (J := J) (P := P) (S := S) (R := R)
theorem p478All : P478All := by intros; exact p478

def P486All : Prop := ∀ {P AX O IP LI F K I R : Type}, P486 (P := P) (AX := AX) (O := O) (IP := IP) (LI := LI) (F := F) (K := K) (I := I) (R := R)
theorem p486All : P486All := by intros; exact p486

def P491All : Prop := ∀ {I IH IF K IP AH AF L R : Type}, P491 (I := I) (IH := IH) (IF := IF) (K := K) (IP := IP) (AH := AH) (AF := AF) (L := L) (R := R)
theorem p491All : P491All := by intros; exact p491

def P496All : Prop := ∀ {I IH IF K IP AH AF : Type}, P496 (I := I) (IH := IH) (IF := IF) (K := K) (IP := IP) (AH := AH) (AF := AF)
theorem p496All : P496All := by intros; exact p496

def P510All : Prop := ∀ {V P K I R : Type}, P510 (V := V) (P := P) (K := K) (I := I) (R := R)
theorem p510All : P510All := by intros; exact p510

def P511All : Prop := ∀ {V P K I R : Type}, P511 (V := V) (P := P) (K := K) (I := I) (R := R)
theorem p511All : P511All := by intros; exact p511

def P525All : Prop := ∀ {V I A : Type}, P525 (V := V) (I := I) (A := A)
theorem p525All : P525All := by intros; exact p525

def P534All : Prop := ∀ {V I A : Type}, P534 (V := V) (I := I) (A := A)
theorem p534All : P534All := by intros; exact p534

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-subarray-repair-{line}", juliaFile := "base/subarray.jl",
    juliaFns := [name], statement := statement, source := source, status := .proven,
    prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.SubarrayRepairLayout
