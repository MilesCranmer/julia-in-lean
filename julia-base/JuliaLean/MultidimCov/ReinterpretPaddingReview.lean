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

def reinterpretPaddingReviewEntries : List Entry := [
  raPaddingEntry "multidimcov-reinterpretarray-padding-map" "showerror, non_padding_bytes, fill_nonpadding_bytes!, array_subpadding, struct_subpadding, packedsize, ispacked, has_bit_padding" "Padding discovery follows primitive bits, recursive fields, cyclic byte compatibility, and datatype padding in source order." "base/reinterpretarray.jl:738-837" ``RAPaddingMapProperty ``raPaddingMapProperty,
  raPaddingEntry "multidimcov-reinterpretarray-packed-copy" "_copytopacked!, _copyfrompacked!" "Packed copying traverses fields in order, copies packed fields directly, recurses for padded fields, and advances exact byte offsets." "base/reinterpretarray.jl:839-877" ``RAPackedCopiesProperty ``raPackedCopiesProperty,
  raPaddingEntry "multidimcov-reinterpretarray-scalar-padding" "_reinterpret, _reinterpret_padding, String(::ReinterpretArray)" "Scalar reinterpret validates bits and packed sizes before direct or padding-aware copy; String permits empty unreadable arrays and otherwise checks readability." "base/reinterpretarray.jl:879-939" ``RAScalarPaddingProperty ``raScalarPaddingProperty,
  raPaddingEntry "multidimcov-reinterpretarray-mapreduce-wrapper" "_mapreduce(::IndexSCartesian2)" "The reduction wrapper checks the second iterator dimension and selects empty reduction or first-to-last implementation." "base/reinterpretarray.jl:943-951" ``RA943Property ``ra943Property,
  raPaddingEntry "multidimcov-reinterpretarray-mapreduce-kernel" "mapreduce_impl(::SCartesianIndex2,blksize)" "The reduction kernel visits every static Cartesian element in sequential mode or splits columns pairwise, with every access in bounds." "base/reinterpretarray.jl:953-979" ``RA953Property ``ra953Property,
  raPaddingEntry "multidimcov-reinterpretarray-mapreduce-default" "mapreduce_impl(::SCartesianIndex2)" "The default wrapper computes pairwise_blocksize before calling the explicit-block kernel." "base/reinterpretarray.jl:981-982" ``RA981Property ``ra981Property,
  raPaddingEntry "multidimcov-reinterpretarray-totuple" "_totuple(::Type{All32},::Union{Array,Memory})" "The fast tuple path checks length, selects the exact prefix view for matching bits elements, reads index one safely, or collects the requested count." "base/reinterpretarray.jl:987-996" ``RA987Property ``ra987Property
]

end JuliaLean.MultidimCov
