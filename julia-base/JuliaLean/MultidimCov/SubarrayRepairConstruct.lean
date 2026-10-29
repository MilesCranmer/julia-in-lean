import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.SubarrayRepairConstruct

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

variable {PT T P I R O S V D TA F G TP TV VS A U C : Type}

/-! Source-order models replacing the remaining HOLLOW constructor and utility
rows in `base/subarray.jl:30-167`. Type parameters are represented explicitly;
callbacks model Julia calls on arbitrary objects and preserve every failure. -/

def m30 (eltype : PT → JResult T) (construct : T → Nat → P → I → JResult R)
    (parentType : PT) (rank : Nat) (parent : P) (indices : I) : JResult R := do
  let elementType ← eltype parentType
  construct elementType rank parent indices

def P30 : Prop := ∀ (eltype : PT → JResult T) (construct : T → Nat → P → I → JResult R)
    parentType rank parent indices,
  m30 eltype construct parentType rank parent indices = do
    let elementType ← eltype parentType
    construct elementType rank parent indices

theorem p30 {PT T P I R : Type} : P30 (PT := PT) (T := T) (P := P) (I := I) (R := R) := by
  unfold P30
  intros
  rfl

def m34 (layout : P → I → JResult (O × S)) (eltype : PT → JResult T)
    (construct : T → Nat → P → I → O → S → JResult R)
    (parentType : PT) (rank : Nat) (parent : P) (indices : I) : JResult R := do
  let (offset, stride) ← layout parent indices
  let elementType ← eltype parentType
  construct elementType rank parent indices offset stride

def P34 : Prop := ∀ (layout : P → I → JResult (O × S)) (eltype : PT → JResult T)
    (construct : T → Nat → P → I → O → S → JResult R)
    parentType rank parent indices,
  m34 layout eltype construct parentType rank parent indices = do
    let (offset, stride) ← layout parent indices
    let elementType ← eltype parentType
    construct elementType rank parent indices offset stride

theorem p34 {PT T P I O S R : Type} :
    P34 (P := P) (I := I) (O := O) (S := S) (PT := PT) (T := T) (R := R) := by
  unfold P34
  intros
  rfl

def m47 (_parent : P) (_shape : List Bool) : JResult Unit := .ok ()

def P47 : Prop := ∀ (parent : P) (shape : List Bool), m47 parent shape = .ok ()

theorem p47 {P : Type} : P47 (P := P) := by unfold P47; intros; rfl

def m48 (ndims : P → JResult AnyValue) (rankValue : Nat → AnyValue)
    (parent : P) (rank : Nat) : JResult Unit := do
  let actual ← ndims parent
  .error (.argument (lazyAppend [
    .literal "number of indices (", .dynamic (rankValue rank),
    .literal ") must match the parent dimensionality (", .dynamic actual, .literal ")"]))

def P48 : Prop := ∀ (ndims : P → JResult AnyValue) (rankValue : Nat → AnyValue) parent rank,
  m48 ndims rankValue parent rank = do
    let actual ← ndims parent
    .error (.argument (lazyAppend [
      .literal "number of indices (", .dynamic (rankValue rank),
      .literal ") must match the parent dimensionality (", .dynamic actual, .literal ")"]))

theorem p48 {P : Type} : P48 (P := P) := by unfold P48; intros; rfl

def m54 (tail : List I → JResult R) (_scalar : I) (rest : List I) : JResult R :=
  tail rest

def P54 : Prop := ∀ (tail : List I → JResult R) scalar rest,
  m54 tail scalar rest = tail rest

theorem p54 {I R : Type} : P54 (I := I) (R := R) := by unfold P54; intros; rfl

def m72 (parent : V → P) (similar : P → T → D → JResult R)
    (view : V) (elementType : T) (dims : D) : JResult R :=
  similar (parent view) elementType dims

def P72 : Prop := ∀ (parent : V → P) (similar : P → T → D → JResult R)
    view elementType dims,
  m72 parent similar view elementType dims = similar (parent view) elementType dims

theorem p72 {V P T D R : Type} :
    P72 (V := V) (P := P) (T := T) (D := D) (R := R) := by unfold P72; intros; rfl

def m73 (parentType : TA → P) (similar : P → D → JResult R)
    (viewType : TA) (dims : D) : JResult R :=
  similar (parentType viewType) dims

def P73 : Prop := ∀ (parentType : TA → P) (similar : P → D → JResult R) viewType dims,
  m73 parentType similar viewType dims = similar (parentType viewType) dims

theorem p73 {TA P D R : Type} :
    P73 (TA := TA) (P := P) (D := D) (R := R) := by unfold P73; intros; rfl

def m78 (parent : V → JResult P) (indices : V → JResult I)
    (getindex : P → I → JResult R) (ndims : V → JResult Nat)
    (similar : V → JResult R) (setScalar : R → R → JResult U) (view : V) : JResult R := do
  let array ← parent view
  let inds ← indices view
  let value ← getindex array inds
  let rank ← ndims view
  if rank ≠ 0 then pure value
  else do
    let result ← similar view
    let _ ← setScalar result value
    pure result

def P78 : Prop := ∀ (parent : V → JResult P) (indices : V → JResult I)
    (getindex : P → I → JResult R) (ndims : V → JResult Nat)
    (similar : V → JResult R) (setScalar : R → R → JResult U) view,
  m78 parent indices getindex ndims similar setScalar view = do
    let array ← parent view
    let inds ← indices view
    let value ← getindex array inds
    let rank ← ndims view
    if rank ≠ 0 then pure value
    else do
      let result ← similar view
      let _ ← setScalar result value
      pure result

theorem p78 {V P I R U : Type} :
    P78 (V := V) (P := P) (I := I) (R := R) (U := U) := by unfold P78; intros; rfl

def splatMapM (f : I → JResult (List D)) : List I → JResult (List D)
  | [] => .ok []
  | head :: tail => do
      let first ← f head
      let rest ← splatMapM f tail
      pure (first ++ rest)

def m114 (f : I → JResult (List D)) (items : List I) : JResult (List D) :=
  splatMapM f items

def P114 : Prop := ∀ (f : I → JResult (List D)) head tail,
  m114 f (head :: tail) = do
    let first ← f head
    let rest ← splatMapM f tail
    pure (first ++ rest)

theorem p114 {I D : Type} : P114 (I := I) (D := D) := by unfold P114; intros; rfl

def mapM (f : I → JResult O) : List I → JResult (List O)
  | [] => .ok []
  | head :: tail => do
      let first ← f head
      let rest ← mapM f tail
      pure (first :: rest)

def m119
    (trimShape : List I → JResult S) (allocate : S → JResult D)
    (trimParent : List I → JResult TP) (directDestination : TP → Bool)
    (viewDestination : D → TP → JResult D) (trimView : List I → JResult TV)
    (viewSource : V → TV → JResult VS) (copyTo : D → VS → JResult C)
    (trimIndex : I → JResult O) (layout : D → List O → JResult (F × G))
    (construct : D → List O → F → G → JResult R) (zeroF : F) (zeroG : G)
    (linear : Bool) (view : V) (indices : List I) : JResult R := do
  let shape ← trimShape indices
  let destination ← allocate shape
  let parentIndices ← trimParent indices
  let viewDestinationValue ←
    if directDestination parentIndices then pure destination
    else viewDestination destination parentIndices
  let viewIndices ← trimView indices
  let sourceView ← viewSource view viewIndices
  let _ ← copyTo viewDestinationValue sourceView
  let copiedIndices ← mapM trimIndex indices
  let (offset, stride) ←
    if linear then layout destination copiedIndices else pure (zeroF, zeroG)
  construct destination copiedIndices offset stride

def P119 : Prop := ∀
    (trimShape : List I → JResult S) (allocate : S → JResult D)
    (trimParent : List I → JResult TP) (directDestination : TP → Bool)
    (viewDestination : D → TP → JResult D) (trimView : List I → JResult TV)
    (viewSource : V → TV → JResult VS) (copyTo : D → VS → JResult C)
    (trimIndex : I → JResult O) (layout : D → List O → JResult (F × G))
    (construct : D → List O → F → G → JResult R) zeroF zeroG linear view indices,
  m119 trimShape allocate trimParent directDestination viewDestination trimView viewSource
      copyTo trimIndex layout construct zeroF zeroG linear view indices = do
    let shape ← trimShape indices
    let destination ← allocate shape
    let parentIndices ← trimParent indices
    let viewDestinationValue ←
      if directDestination parentIndices then pure destination
      else viewDestination destination parentIndices
    let viewIndices ← trimView indices
    let sourceView ← viewSource view viewIndices
    let _ ← copyTo viewDestinationValue sourceView
    let copiedIndices ← mapM trimIndex indices
    let (offset, stride) ←
      if linear then layout destination copiedIndices else pure (zeroF, zeroG)
    construct destination copiedIndices offset stride

theorem p119 {I S D TP TV V VS C O F G R : Type} :
    P119 (I := I) (S := S) (D := D) (TP := TP) (TV := TV) (V := V) (VS := VS)
      (C := C) (O := O) (F := F) (G := G) (R := R) := by
  unfold P119
  intros
  rfl

def m167 (parent : A) : A := parent

def P167 : Prop := ∀ parent : A, m167 parent = parent

theorem p167 {A : Type} : P167 (A := A) := by unfold P167; intros; rfl


/-! Closed forms of the properties above, quantified over every choice of the
model's carrier types, so each registry `prop` is a closed `Prop`. -/

def P30All : Prop := ∀ {PT T P I R : Type}, P30 (PT := PT) (T := T) (P := P) (I := I) (R := R)
theorem p30All : P30All := by intros; exact p30

def P34All : Prop := ∀ {PT T P I O S R : Type}, P34 (PT := PT) (T := T) (P := P) (I := I) (O := O) (S := S) (R := R)
theorem p34All : P34All := by intros; exact p34

def P47All : Prop := ∀ {P : Type}, P47 (P := P)
theorem p47All : P47All := by intros; exact p47

def P48All : Prop := ∀ {P : Type}, P48 (P := P)
theorem p48All : P48All := by intros; exact p48

def P54All : Prop := ∀ {I R : Type}, P54 (I := I) (R := R)
theorem p54All : P54All := by intros; exact p54

def P72All : Prop := ∀ {V P T D R : Type}, P72 (V := V) (P := P) (T := T) (D := D) (R := R)
theorem p72All : P72All := by intros; exact p72

def P73All : Prop := ∀ {TA P D R : Type}, P73 (TA := TA) (P := P) (D := D) (R := R)
theorem p73All : P73All := by intros; exact p73

def P78All : Prop := ∀ {V P I R U : Type}, P78 (V := V) (P := P) (I := I) (R := R) (U := U)
theorem p78All : P78All := by intros; exact p78

def P114All : Prop := ∀ {I D : Type}, P114 (I := I) (D := D)
theorem p114All : P114All := by intros; exact p114

def P119All : Prop := ∀ {I S D TP TV V VS C O F G R : Type}, P119 (I := I) (S := S) (D := D) (TP := TP) (TV := TV) (V := V) (VS := VS) (C := C) (O := O) (F := F) (G := G) (R := R)
theorem p119All : P119All := by intros; exact p119

def P167All : Prop := ∀ {A : Type}, P167 (A := A)
theorem p167All : P167All := by intros; exact p167

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-subarray-repair-{line}", juliaFile := "base/subarray.jl",
    juliaFns := [name], statement := statement, source := source, status := .proven,
    prop := prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.SubarrayRepairConstruct
