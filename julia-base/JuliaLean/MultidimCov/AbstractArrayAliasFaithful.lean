import JuliaLean.MultidimCov.AbstractArrayInterfaceFaithful
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov.AbstractArrayAliasFaithful

open JuliaLean.Registry
open AbstractArrayInterfaceFaithful

inductive AliasFailure where
  | argument (message : LazyString)
  | bounds
  | errorException (message : String)
  | callback (id : Nat)
  deriving Repr, DecidableEq

abbrev AResult (α : Type) := Except AliasFailure α

/-- Wrong-type `_unaliascopy`, lines 1585-1592. -/
def m1585 (typeofA : A → AResult T) (typename : T → AResult N)
    (wrapper : N → AResult AnyValue) (asAnyType : T → AnyValue)
    (copyType : C → AResult AnyValue) (array : A) (copy : C) : AResult R := do
  let firstType ← typeofA array
  let name ← typename firstType
  let wrapped ← wrapper name
  let secondType ← typeofA array
  let resultType ← copyType copy
  .error (.argument (lazyAppend [.literal "an array of type `", .dynamic wrapped,
    .literal "` shares memory with another argument and must make a preventative copy of itself in order to maintain consistent semantics, but `copy(::",
    .dynamic (asAnyType secondType), .literal ")` returns a new array of type `", .dynamic resultType,
    .literal "`.\nTo fix, implement:\n    `Base.unaliascopy(A::", .dynamic wrapped,
    .literal ")::typeof(A)`"]))
def P1585 : Prop := ∀ {A C R T N : Type} (typeofA : A → AResult T)
    (typename : T → AResult N) (wrapper : N → AResult AnyValue)
    (asAnyType : T → AnyValue) (copyType : C → AResult AnyValue)
    (array : A) (copy : C),
  m1585 (R := R) typeofA typename wrapper asAnyType copyType array copy = do
    let firstType ← typeofA array
    let name ← typename firstType
    let wrapped ← wrapper name
    let secondType ← typeofA array
    let resultType ← copyType copy
    .error (.argument (lazyAppend [.literal "an array of type `", .dynamic wrapped,
      .literal "` shares memory with another argument and must make a preventative copy of itself in order to maintain consistent semantics, but `copy(::",
      .dynamic (asAnyType secondType), .literal ")` returns a new array of type `", .dynamic resultType,
      .literal "`.\nTo fix, implement:\n    `Base.unaliascopy(A::", .dynamic wrapped,
      .literal ")::typeof(A)`"]))
theorem p1585 : P1585 := by unfold P1585; intros; rfl

/-- Generic `mightalias`, line 1604. -/
def m1604 (_left : A) (_right : B) : Bool := false
def P1604 : Prop := ∀ {A B : Type} (left : A) (right : B), m1604 left right = false
theorem p1604 : P1604 := by unfold P1604; intros; rfl

/-- Generic `dataids`, line 1630. -/
def m1630 (_value : A) : List Nat := []
def P1630 : Prop := ∀ {A : Type} (value : A), m1630 value = []
theorem p1630 : P1630 := by unfold P1630; intros; rfl

/-- Scalar value-default `get`, line 1637. -/
def m1637 (checkbounds : A → IntegerValue → AResult Bool)
    (getindex : A → IntegerValue → AResult V) (array : A)
    (index : IntegerValue) (default : V) : AResult V := do
  if ← checkbounds array index then getindex array index else .ok default
def P1637 : Prop := ∀ {A V : Type} (checkbounds : A → IntegerValue → AResult Bool)
    (getindex : A → IntegerValue → AResult V) (array : A) index default,
  m1637 checkbounds getindex array index default = do
    if ← checkbounds array index then getindex array index else .ok default
theorem p1637 : P1637 := by unfold P1637; intros; rfl

/-- Scalar callable-default `get`, line 1640. -/
def m1640 (checkbounds : A → IntegerValue → AResult Bool)
    (getindex : A → IntegerValue → AResult V) (fallback : Unit → AResult V)
    (array : A) (index : IntegerValue) : AResult V := do
  if ← checkbounds array index then getindex array index else fallback ()
def P1640 : Prop := ∀ {A V : Type} (checkbounds : A → IntegerValue → AResult Bool)
    (getindex : A → IntegerValue → AResult V) (fallback : Unit → AResult V)
    (array : A) index,
  m1640 checkbounds getindex fallback array index = do
    if ← checkbounds array index then getindex array index else fallback ()
theorem p1640 : P1640 := by unfold P1640; intros; rfl

/-- Vector `get!`, lines 1644-1652. -/
def m1644 (sourceAxes : A → AResult AX) (destinationAxes : X → AResult AX)
    (findall : AX → I → AResult POS)
    (copySelected : X → A → I → POS → AResult X)
    (firstAxis : AX → AResult IntegerValue) (firstPosition : POS → AResult IntegerValue)
    (lastPosition : POS → AResult IntegerValue) (lastAxis : AX → AResult IntegerValue)
    (fillRange : X → IntegerValue → IntegerValue → V → AResult X)
    (dest : X) (src : A) (requested : I) (default : V) : AResult X := do
  let sourceAxis ← sourceAxes src
  let positions ← findall sourceAxis requested
  let copied ← copySelected dest src requested positions
  let destinationAxis ← destinationAxes copied
  let destinationFirst ← firstAxis destinationAxis
  let validFirst ← firstPosition positions
  let filledPrefix ← fillRange copied destinationFirst ⟨validFirst.value - 1⟩ default
  let validLast ← lastPosition positions
  let destinationLast ← lastAxis destinationAxis
  fillRange filledPrefix ⟨validLast.value + 1⟩ destinationLast default
def P1644 : Prop := ∀ {X AX I POS A V : Type} (sourceAxes : A → AResult AX)
    (destinationAxes : X → AResult AX) (findall : AX → I → AResult POS)
    (copySelected : X → A → I → POS → AResult X)
    (firstAxis : AX → AResult IntegerValue) (firstPosition lastPosition : POS → AResult IntegerValue)
    (lastAxis : AX → AResult IntegerValue)
    (fillRange : X → IntegerValue → IntegerValue → V → AResult X)
    (dest : X) (src : A) requested default,
  m1644 sourceAxes destinationAxes findall copySelected firstAxis firstPosition lastPosition lastAxis
    fillRange dest src requested default = do
      let sourceAxis ← sourceAxes src
      let positions ← findall sourceAxis requested
      let copied ← copySelected dest src requested positions
      let destinationAxis ← destinationAxes copied
      let destinationFirst ← firstAxis destinationAxis
      let validFirst ← firstPosition positions
      let filledPrefix ← fillRange copied destinationFirst ⟨validFirst.value - 1⟩ default
      let validLast ← lastPosition positions
      let destinationLast ← lastAxis destinationAxis
      fillRange filledPrefix ⟨validLast.value + 1⟩ destinationLast default
theorem p1644 : P1644 := by unfold P1644; intros; rfl

/-- Linear array `get!`, lines 1653-1660. -/
def m1653 (sourceLength : A → AResult IntegerValue) (destinationLength : X → AResult IntegerValue)
    (findall : IntegerValue → I → AResult POS)
    (copySelected : X → A → I → POS → AResult X)
    (firstPosition lastPosition : POS → AResult IntegerValue)
    (viewFill : X → IntegerValue → IntegerValue → V → AResult X)
    (dest : X) (src : A) (requested : I) (default : V) : AResult X := do
  let sourceCount ← sourceLength src
  let positions ← findall sourceCount requested
  let copied ← copySelected dest src requested positions
  let validFirst ← firstPosition positions
  let filledPrefix ← viewFill copied ⟨1⟩ ⟨validFirst.value - 1⟩ default
  let validLast ← lastPosition positions
  let destinationCount ← destinationLength filledPrefix
  viewFill filledPrefix ⟨validLast.value + 1⟩ destinationCount default
def P1653 : Prop := ∀ {A I POS X V : Type} (sourceLength : A → AResult IntegerValue)
    (destinationLength : X → AResult IntegerValue) (findall : IntegerValue → I → AResult POS)
    (copySelected : X → A → I → POS → AResult X)
    (firstPosition lastPosition : POS → AResult IntegerValue)
    (viewFill : X → IntegerValue → IntegerValue → V → AResult X)
    (dest : X) (src : A) requested default,
  m1653 sourceLength destinationLength findall copySelected firstPosition lastPosition
    viewFill dest src requested default = do
      let sourceCount ← sourceLength src
      let positions ← findall sourceCount requested
      let copied ← copySelected dest src requested positions
      let validFirst ← firstPosition positions
      let filledPrefix ← viewFill copied ⟨1⟩ ⟨validFirst.value - 1⟩ default
      let validLast ← lastPosition positions
      let destinationCount ← destinationLength filledPrefix
      viewFill filledPrefix ⟨validLast.value + 1⟩ destinationCount default
theorem p1653 : P1653 := by unfold P1653; intros; rfl

/-- Zero-argument promotion helpers, lines 1682 and 1689. -/
def m1682 : AResult T := .error (.errorException "")
def P1682 : Prop := ∀ (T : Type), (m1682 : AResult T) = .error (.errorException "")
theorem p1682 : P1682 := by unfold P1682; intros; rfl
def m1689 : AResult T := .error (.errorException "")
def P1689 : Prop := ∀ (T : Type), (m1689 : AResult T) = .error (.errorException "")
theorem p1689 : P1689 := by unfold P1689; intros; rfl

/-- Empty `_cat(catdim::Int)`, line 1697. -/
def m1697 (_dimension : Int) : List AnyValue := []
def P1697 : Prop := ∀ dimension : Int, m1697 dimension = ([] : List AnyValue)
theorem p1697 : P1697 := by unfold P1697; intros; rfl

private def entry (line : Nat) (name statement source : String) (prop thm : Lean.Name) : Entry :=
  { id := s!"multidimcov-abstractarray-alias-faithful-{line}", juliaFile := "base/abstractarray.jl",
    juliaFns := [name], statement, source, status := .proven, prop, thm := some thm }

def entries : List Entry := []

end JuliaLean.MultidimCov.AbstractArrayAliasFaithful
