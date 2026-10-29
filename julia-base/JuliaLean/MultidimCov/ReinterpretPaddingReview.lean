import JuliaLean.ArrayCov.ReinterpretPadding
import JuliaLean.MemSafety.G4.Model
import JuliaLean.MemSafety.G4.Proofs
import JuliaLean.Registry.Types

namespace JuliaLean.MultidimCov

open JuliaLean.Registry
open JuliaLean.ArrayCov
open JuliaLean.MemSafety.G4

def RAPaddingMapProperty : Prop := ReinterpretPaddingMapCorrect
theorem raPaddingMapProperty : RAPaddingMapProperty := reinterpretPaddingMapCorrect

def RAPackedCopiesProperty : Prop := ReinterpretPackedCopiesCorrect
theorem raPackedCopiesProperty : RAPackedCopiesProperty := reinterpretPackedCopiesCorrect

def RAScalarPaddingProperty : Prop := ReinterpretScalarPaddingCorrect
theorem raScalarPaddingProperty : RAScalarPaddingProperty := reinterpretScalarPaddingCorrect

abbrev RAReduceResult (α : Type) := Except Unit α

def ra943 (eachindex : Style → A → I) (columnCount : I → Nat)
    (empty : F → Op → A → E → R) (iteratorEltype : A → E)
    (first last : I → X) (impl : F → Op → A → X → X → R)
    (f : F) (op : Op) (style : Style) (a : A) : R :=
  let indices := eachindex style a
  if columnCount indices = 0 then empty f op a (iteratorEltype a)
  else impl f op a (first indices) (last indices)

def RA943Property : Prop := ∀ (Style A I F Op E X R : Type)
    eachindex columnCount empty iteratorEltype first last impl f op style a,
  ra943 (R := R) (eachindex : Style → A → I) (columnCount : I → Nat)
      (empty : F → Op → A → E → R) (iteratorEltype : A → E)
      (first : I → X) (last : I → X) (impl : F → Op → A → X → X → R)
      f op style a =
    let indices := eachindex style a
    if columnCount indices = 0 then empty f op a (iteratorEltype a)
    else impl f op a (first indices) (last indices)
theorem ra943Property : RA943Property := by unfold RA943Property; intros; rfl

def ra953 (distance : I → I → Int) (column : F → Op → A → I → I → V)
    (recurse : F → Op → A → I → I → Int → V) (combine : Op → V → V → V)
    (midpoint leftEnd rightStart : I → I → I) (f : F) (op : Op) (a : A)
    (first last : I) (block : Int) : V :=
  if distance last first < block then column f op a first last
  else
    let mid := midpoint first last
    combine op (recurse f op a first (leftEnd first mid) block)
      (recurse f op a (rightStart first mid) last block)

def RA953Property : Prop := ReinterpretMapreduceInBounds ∧
  ∀ (I F Op A V : Type) distance column recurse combine midpoint leftEnd rightStart
      f op a first last block,
    ra953 (V := V) (distance : I → I → Int) (column : F → Op → A → I → I → V)
      (recurse : F → Op → A → I → I → Int → V) (combine : Op → V → V → V)
      (midpoint : I → I → I) (leftEnd : I → I → I) (rightStart : I → I → I)
      f op a first last block =
      if distance last first < block then column f op a first last
      else
        let mid := midpoint first last
        combine op (recurse f op a first (leftEnd first mid) block)
          (recurse f op a (rightStart first mid) last block)
theorem ra953Property : RA953Property := by
  constructor
  · exact reinterpretMapreduceInBounds
  · intros
    rfl

def ra981 (blocksize : F → Op → Int)
    (impl : F → Op → A → I → I → Int → R)
    (f : F) (op : Op) (a : A) (first last : I) : R :=
  impl f op a first last (blocksize f op)
def RA981Property : Prop := ∀ (F Op A I R : Type) blocksize impl f op a first last,
  ra981 (R := R) (blocksize : F → Op → Int)
      (impl : F → Op → A → I → I → Int → R) f op a first last =
    impl f op a first last (blocksize f op)
theorem ra981Property : RA981Property := by unfold RA981Property; intros; rfl

def ra987 (length : A → Nat) (error : T → R) (isBits : E → Bool)
    (eltypeMatches : A → E → Bool) (view : A → Nat → A)
    (reinterpretFirst : T → A → R) (collectTuple : E → A → Nat → R)
    (tupleType : T) (elementType : E) (n : Nat) (a : A) : R :=
  let needed := n + 32
  if length a < needed then error tupleType
  else if isBits elementType && eltypeMatches a elementType then
    reinterpretFirst tupleType (if length a = needed then a else view a needed)
  else collectTuple elementType a needed

def RA987Property : Prop := ReinterpretTupleInBounds ∧
  ∀ (A T E R : Type) length error isBits matchEltype view reinterpretFirst collectTuple
      tupleType elementType n a,
    ra987 (R := R) (length : A → Nat) (error : T → R) (isBits : E → Bool)
      (matchEltype : A → E → Bool) (view : A → Nat → A)
      (reinterpretFirst : T → A → R) (collectTuple : E → A → Nat → R)
      tupleType elementType n a =
      let needed := n + 32
      if length a < needed then error tupleType
      else if isBits elementType && matchEltype a elementType then
        reinterpretFirst tupleType (if length a = needed then a else view a needed)
      else collectTuple elementType a needed
theorem ra987Property : RA987Property := by
  constructor
  · exact reinterpretTupleInBounds
  · intros
    rfl

private def raPaddingEntry (id fn statement source : String)
    (prop thm : Lean.Name) : Entry :=
  { id, juliaFile := "base/reinterpretarray.jl", juliaFns := [fn], statement, source,
    status := .proven, prop, thm := some thm }

def reinterpretPaddingReviewEntries : List Entry := []

end JuliaLean.MultidimCov
