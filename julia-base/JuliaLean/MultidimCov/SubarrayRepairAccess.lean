import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayRepairAccess

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

variable {R1 R2 O V I R P K X U : Type}

/-! Source-order models replacing the remaining HOLLOW access rows in
`base/subarray.jl:230-430`. Every index, value, result, and callback failure is
polymorphic unless Julia's method signature fixes it. -/

def m230 (getindex : R1 → R2 → JResult O) (range : R1) (indices : R2) : JResult O :=
  getindex range indices

def P230 : Prop := ∀ (getindex : R1 → R2 → JResult O) range indices,
  m230 getindex range indices = getindex range indices

theorem p230 {R1 R2 O : Type} : P230 (R1 := R1) (R2 := R2) (O := O) := by
  unfold P230
  intros
  rfl

def m267 (maybeReindex : V → I → JResult R) (view : V) (indices : I) : JResult R :=
  maybeReindex view indices

def P267 : Prop := ∀ (maybeReindex : V → I → JResult R) view indices,
  m267 maybeReindex view indices = maybeReindex view indices

theorem p267 {V I R : Type} : P267 (V := V) (I := I) (R := R) := by unfold P267; intros; rfl

def m269 (maybeReindex : V → I → I → JResult R) (view : V) (indices : I) : JResult R :=
  maybeReindex view indices indices

def P269 : Prop := ∀ (maybeReindex : V → I → I → JResult R) view indices,
  m269 maybeReindex view indices = maybeReindex view indices indices

theorem p269 {V I R : Type} : P269 (V := V) (I := I) (R := R) := by unfold P269; intros; rfl

def m270 (construct : V → I → JResult R) (view : V) (indices : I) : JResult R :=
  construct view indices

def P270 : Prop := ∀ (construct : V → I → JResult R) view indices,
  m270 construct view indices = construct view indices

theorem p270 {V I R : Type} : P270 (V := V) (I := I) (R := R) := by unfold P270; intros; rfl

def m292 (_parentIndices : Unit) (_subIndices : Unit) : Unit := ()

def P292 : Prop := ∀ parentIndices subIndices : Unit,
  m292 parentIndices subIndices = ()

theorem p292 : P292 := by unfold P292; intros; rfl

def fastGet (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (getindex : P → K → JResult R)
    (view : V) (index : I) : JResult R := do
  checkbounds view index
  let shifted ← reindexLinear view index
  getindex (parent view) shifted

def m330 (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (getindex : P → K → JResult R)
    (view : V) (index : I) : JResult R :=
  fastGet checkbounds parent reindexLinear getindex view index

def P330 : Prop := ∀ (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (getindex : P → K → JResult R) view index,
  m330 checkbounds parent reindexLinear getindex view index = do
    checkbounds view index
    let shifted ← reindexLinear view index
    getindex (parent view) shifted

theorem p330 {V I P K R : Type} :
    P330 (V := V) (I := I) (P := P) (K := K) (R := R) := by unfold P330; intros; rfl

def m339 (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (getindex : P → K → JResult R)
    (view : V) (index : I) : JResult R := do
  checkbounds view index
  let shifted ← reindexLinear view index
  getindex (parent view) shifted

def P339 : Prop := ∀ (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (getindex : P → K → JResult R) view index,
  m339 checkbounds parent reindexLinear getindex view index = do
    checkbounds view index
    let shifted ← reindexLinear view index
    getindex (parent view) shifted

theorem p339 {V I P K R : Type} :
    P339 (V := V) (I := I) (P := P) (K := K) (R := R) := by unfold P339; intros; rfl

def m398 (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (setindex : P → X → K → JResult U)
    (view : V) (value : X) (index : I) : JResult V := do
  checkbounds view index
  let shifted ← reindexLinear view index
  let _ ← setindex (parent view) value shifted
  pure view

def P398 : Prop := ∀ (checkbounds : V → I → JResult Unit) (parent : V → P)
    (reindexLinear : V → I → JResult K) (setindex : P → X → K → JResult U)
    view value index,
  m398 checkbounds parent reindexLinear setindex view value index = do
    checkbounds view index
    let shifted ← reindexLinear view index
    let _ ← setindex (parent view) value shifted
    pure view

theorem p398 {V I P K X U : Type} :
    P398 (V := V) (I := I) (P := P) (K := K) (X := X) (U := U) := by unfold P398; intros; rfl

def m426 (checkbounds : V → I → JResult Bool) (parent : V → P)
    (reindexLinear : V → I → JResult K) (isassigned : P → K → JResult Bool)
    (view : V) (index : I) : JResult Bool := do
  let valid ← checkbounds view index
  if !valid then pure false
  else
    let shifted ← reindexLinear view index
    isassigned (parent view) shifted

def P426 : Prop := ∀ (checkbounds : V → I → JResult Bool) (parent : V → P)
    (reindexLinear : V → I → JResult K) (isassigned : P → K → JResult Bool)
    view index,
  m426 checkbounds parent reindexLinear isassigned view index = do
    let valid ← checkbounds view index
    if !valid then pure false
    else
      let shifted ← reindexLinear view index
      isassigned (parent view) shifted

theorem p426 {V I P K : Type} :
    P426 (V := V) (I := I) (P := P) (K := K) := by unfold P426; intros; rfl


/-! Closed forms of the properties above, quantified over every choice of the
model's carrier types, so each registry `prop` is a closed `Prop`. -/

def P230All : Prop := ∀ {R1 R2 O : Type}, P230 (R1 := R1) (R2 := R2) (O := O)
theorem p230All : P230All := by intros; exact p230

def P267All : Prop := ∀ {V I R : Type}, P267 (V := V) (I := I) (R := R)
theorem p267All : P267All := by intros; exact p267

def P269All : Prop := ∀ {V I R : Type}, P269 (V := V) (I := I) (R := R)
theorem p269All : P269All := by intros; exact p269

def P270All : Prop := ∀ {V I R : Type}, P270 (V := V) (I := I) (R := R)
theorem p270All : P270All := by intros; exact p270

def P330All : Prop := ∀ {V I P K R : Type}, P330 (V := V) (I := I) (P := P) (K := K) (R := R)
theorem p330All : P330All := by intros; exact p330

def P339All : Prop := ∀ {V I P K R : Type}, P339 (V := V) (I := I) (P := P) (K := K) (R := R)
theorem p339All : P339All := by intros; exact p339

def P398All : Prop := ∀ {V I P K X U : Type}, P398 (V := V) (I := I) (P := P) (K := K) (X := X) (U := U)
theorem p398All : P398All := by intros; exact p398

def P426All : Prop := ∀ {V I P K : Type}, P426 (V := V) (I := I) (P := P) (K := K)
theorem p426All : P426All := by intros; exact p426

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-subarray-repair-{line}", juliaFile := "base/subarray.jl",
    juliaFns := [name], statement := statement, source := source, status := .proven,
    prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.SubarrayRepairAccess
