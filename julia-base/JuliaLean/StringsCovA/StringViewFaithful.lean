import JuliaLean.StringsCovA.StringView

namespace JuliaLean.StringsCovA.StringViewFaithful

open JuliaLean
open JuliaLean.StringsCovA.StringView

abbrev Bytes := List UInt8

def ctor (typedCtor : Bytes → View) (v : Bytes) := typedCtor v
def CtorProperty : Prop := ∀ typedCtor v, ctor typedCtor v = typedCtor v
theorem ctor_proven : CtorProperty := by unfold CtorProperty; intros; rfl

def toVector (codeunits : View → Bytes) (s : View) := codeunits s
def ToVectorProperty : Prop := ∀ codeunits s, toVector codeunits s = codeunits s
theorem toVector_proven : ToVectorProperty := by unfold ToVectorProperty; intros; rfl

def toArray (toVec : View → Bytes) (s : View) := toVec s
def ToArrayProperty : Prop := ∀ toVec s, toArray toVec s = toVec s
theorem toArray_proven : ToArrayProperty := by unfold ToArrayProperty; intros; rfl

def toStringGeneric (ncodeunits : View → Nat) (codeunits : View → Bytes)
    (stringVector : Nat → Bytes) (copyto : Bytes → Bytes → Bytes) (stringCtor : Bytes → Bytes)
    (s : View) : Bytes :=
  let out := stringVector (ncodeunits s)
  stringCtor (copyto out (codeunits s))
def ToStringGenericProperty : Prop := ∀ ncu cu sv cp ctor s,
  toStringGeneric ncu cu sv cp ctor s = ctor (cp (sv (ncu s)) (cu s))
theorem toStringGeneric_proven : ToStringGenericProperty := by unfold ToStringGenericProperty; intros; rfl

def copyView (copyData : Bytes → Bytes) (s : View) : View := ⟨copyData s.bytes, s.address⟩
def CopyViewProperty : Prop := ∀ copyData s, (copyView copyData s).bytes = copyData s.bytes
theorem copyView_proven : CopyViewProperty := by unfold CopyViewProperty; intros; rfl

def symbol (ccall : Nat → Nat → Nat) (s : View) (ncodeunits : View → Nat) := ccall s.address (ncodeunits s)
def SymbolProperty : Prop := ∀ ccall s ncu, symbol ccall s ncu = ccall s.address (ncu s)
theorem symbol_proven : SymbolProperty := by unfold SymbolProperty; intros; rfl

def pointer (s : View) : Nat := s.address
def PointerProperty : Prop := ∀ s, pointer s = s.address
theorem pointer_proven : PointerProperty := by unfold PointerProperty; intros; rfl

def pointerAt (s : View) (i : Int) : Int := s.address + i - 1
def PointerAtProperty : Prop := ∀ s i, pointerAt s i = s.address + i - 1
theorem pointerAt_proven : PointerAtProperty := by unfold PointerAtProperty; intros; rfl

def subPointer (s : SubView) : Nat := s.parent.address + s.offset
def SubPointerProperty : Prop := ∀ s, subPointer s = s.parent.address + s.offset
theorem subPointer_proven : SubPointerProperty := by unfold SubPointerProperty; intros; rfl

def subPointerAt (s : SubView) (i : Int) : Int := s.parent.address + s.offset + i - 1
def SubPointerAtProperty : Prop := ∀ s i, subPointerAt s i = s.parent.address + s.offset + i - 1
theorem subPointerAt_proven : SubPointerAtProperty := by unfold SubPointerAtProperty; intros; rfl

def unsafeConvertU8 (s : View) := pointer s
def UnsafeConvertU8Property : Prop := ∀ s, unsafeConvertU8 s = pointer s
theorem unsafeConvertU8_proven : UnsafeConvertU8Property := by unfold UnsafeConvertU8Property; intros; rfl

def unsafeConvertI8 (convert : Nat → Nat) (s : View) := convert (pointer s)
def UnsafeConvertI8Property : Prop := ∀ convert s, unsafeConvertI8 convert s = convert (pointer s)
theorem unsafeConvertI8_proven : UnsafeConvertI8Property := by unfold UnsafeConvertI8Property; intros; rfl

def toStringDense (unsafeString : Nat → Nat → Bytes) (ncodeunits : View → Nat) (s : View) :=
  unsafeString (pointer s) (ncodeunits s)
def ToStringDenseProperty : Prop := ∀ us ncu s, toStringDense us ncu s = us (pointer s) (ncu s)
theorem toStringDense_proven : ToStringDenseProperty := by unfold ToStringDenseProperty; intros; rfl

def cconvertU8 (s : View) := s
def CconvertU8Property : Prop := ∀ s, cconvertU8 s = s
theorem cconvertU8_proven : CconvertU8Property := by unfold CconvertU8Property; intros; rfl

def cconvertI8 (s : View) := s
def CconvertI8Property : Prop := ∀ s, cconvertI8 s = s
theorem cconvertI8_proven : CconvertI8Property := by unfold CconvertI8Property; intros; rfl

def sizeof (s : View) : Nat := s.bytes.length
def SizeofProperty : Prop := ∀ s, sizeof s = s.bytes.length
theorem sizeof_proven : SizeofProperty := by unfold SizeofProperty; intros; rfl

def ncodeunits (s : View) : Nat := s.bytes.length
def NcodeunitsProperty : Prop := ∀ s, ncodeunits s = s.bytes.length
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl

def codeunitType (_s : View) : Nat := 8
def CodeunitTypeProperty : Prop := ∀ s, codeunitType s = 8
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl

def codeunit (s : View) (i : Int) : Jl UInt8 :=
  if 1 ≤ i ∧ i ≤ s.bytes.length then .ok (s.bytes.getD (i.toNat - 1) 0) else .error .boundsError
def CodeunitProperty : Prop := ∀ s i, codeunit s i =
  if 1 ≤ i ∧ i ≤ s.bytes.length then .ok (s.bytes.getD (i.toNat - 1) 0) else .error .boundsError
theorem codeunit_proven : CodeunitProperty := by unfold CodeunitProperty; intros; rfl

def codeunits (s : View) : Bytes := s.bytes
def CodeunitsProperty : Prop := ∀ s, codeunits s = s.bytes
theorem codeunits_proven : CodeunitsProperty := by unfold CodeunitsProperty; intros; rfl

def subCodeunits (s : SubView) : Bytes := (s.parent.bytes.drop s.offset).take s.ncodeunits
def SubCodeunitsProperty : Prop := ∀ s, subCodeunits s = (s.parent.bytes.drop s.offset).take s.ncodeunits
theorem subCodeunits_proven : SubCodeunitsProperty := by unfold SubCodeunitsProperty; intros; rfl

def cmp (cmpBytes : Bytes → Bytes → Int) (a b : View) := cmpBytes (codeunits a) (codeunits b)
def CmpProperty : Prop := ∀ cmpBytes a b, cmp cmpBytes a b = cmpBytes (codeunits a) (codeunits b)
theorem cmp_proven : CmpProperty := by unfold CmpProperty; intros; rfl

def eq (a b : View) : Bool := codeunits a == codeunits b
def EqProperty : Prop := ∀ a b, eq a b = (codeunits a == codeunits b)
theorem eq_proven : EqProperty := by unfold EqProperty; intros; rfl

def typeminCodeunits : View := ⟨[], 0⟩
def TypeminCodeunitsProperty : Prop := ∀ _u : Unit, typeminCodeunits.bytes = []
theorem typeminCodeunits_proven : TypeminCodeunitsProperty := by unfold TypeminCodeunitsProperty; intros; rfl

def typeminType (kind : BackingKind) : Jl View := StringView.typeminType kind
def TypeminTypeProperty : Prop := ∀ kind, typeminType kind = .ok ⟨[], 0⟩
theorem typeminType_refuted : ¬ TypeminTypeProperty := by
  intro h
  have hs := h .subarray
  change (Except.error (.methodError "SubArray()") : Jl View) = .ok ⟨[], 0⟩ at hs
  cases hs

def typeminValue (typeminType : BackingKind → Jl View) (kind : BackingKind) := typeminType kind
def TypeminValueProperty : Prop := ∀ typeminType kind, typeminValue typeminType kind = typeminType kind
theorem typeminValue_proven : TypeminValueProperty := by unfold TypeminValueProperty; intros; rfl

def one (typeminType : BackingKind → Jl View) (kind : BackingKind) := typeminType kind
def OneProperty : Prop := ∀ typeminType kind, one typeminType kind = typeminType kind
theorem one_proven : OneProperty := by unfold OneProperty; intros; rfl

def oneunit (typeminType : BackingKind → Jl View) (kind : BackingKind) := typeminType kind
def OneunitProperty : Prop := ∀ typeminType kind, oneunit typeminType kind = typeminType kind
theorem oneunit_proven : OneunitProperty := by unfold OneunitProperty; intros; rfl

def isascii (codeunits : View → Bytes) (asciiBytes : Bytes → Bool) (s : View) := asciiBytes (codeunits s)
def IsasciiProperty : Prop := ∀ cu ascii s, isascii cu ascii s = ascii (cu s)
theorem isascii_proven : IsasciiProperty := by unfold IsasciiProperty; intros; rfl

def hash (hashBytes : Nat → Nat → UInt64 → UInt64 → UInt64) (s : View) (h secret : UInt64) :=
  hashBytes s.address s.bytes.length h secret
def HashProperty : Prop := ∀ hb s h secret, hash hb s h secret = hb s.address s.bytes.length h secret
theorem hash_proven : HashProperty := by unfold HashProperty; intros; rfl

def write (writeBytes : Bytes → Nat) (s : View) := writeBytes (codeunits s)
def WriteProperty : Prop := ∀ wb s, write wb s = wb (codeunits s)
theorem write_proven : WriteProperty := by unfold WriteProperty; intros; rfl

def print (writeView : View → Nat) (s : View) : Unit := let _ := writeView s; ()
def PrintProperty : Prop := ∀ w s, print w s = ()
theorem print_proven : PrintProperty := by unfold PrintProperty; intros; rfl

def thisindInteger (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i
def ThisindIntegerProperty : Prop := ∀ helper s i, thisindInteger helper s i = helper s i
theorem thisindInteger_proven : ThisindIntegerProperty := by unfold ThisindIntegerProperty; intros; rfl

def thisindInt (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i
def ThisindIntProperty : Prop := ∀ helper s i, thisindInt helper s i = helper s i
theorem thisindInt_proven : ThisindIntProperty := by unfold ThisindIntProperty; intros; rfl

def nextindInteger (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i
def NextindIntegerProperty : Prop := ∀ helper s i, nextindInteger helper s i = helper s i
theorem nextindInteger_proven : NextindIntegerProperty := by unfold NextindIntegerProperty; intros; rfl

def nextindInt (helper : View → Int → Jl Int) (s : View) (i : Int) := helper s i
def NextindIntProperty : Prop := ∀ helper s i, nextindInt helper s i = helper s i
theorem nextindInt_proven : NextindIntProperty := by unfold NextindIntProperty; intros; rfl

def isvalid (checkbounds : View → Int → Bool) (thisind : View → Int → Int) (s : View) (i : Int) :=
  checkbounds s i && thisind s i == i
def IsvalidProperty : Prop := ∀ cb ti s i, isvalid cb ti s i = (cb s i && ti s i == i)
theorem isvalid_proven : IsvalidProperty := by unfold IsvalidProperty; intros; rfl

def getindexRange (valid : Bytes → Int → Bool) (next : Bytes → Int → Int)
    (s : View) (i j : Int) : Jl View :=
  if j < i then .ok ⟨[], s.address⟩
  else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
  else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
  else
    let stop := next s.bytes j - 1
    .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat, s.address + i.toNat - 1⟩
def GetindexRangeProperty : Prop := ∀ valid next s i j, getindexRange valid next s i j =
  if j < i then .ok ⟨[], s.address⟩
  else if !(1 ≤ i ∧ j ≤ s.bytes.length) then .error .boundsError
  else if !valid s.bytes i || !valid s.bytes j then .error (.argumentError "StringIndexError")
  else let stop := next s.bytes j - 1
    .ok ⟨(s.bytes.drop (i.toNat - 1)).take (stop - i + 1).toNat, s.address + i.toNat - 1⟩
theorem getindexRange_proven : GetindexRangeProperty := by unfold GetindexRangeProperty; intros; rfl

def chomp (s : View) : View :=
  let ncu := s.bytes.length
  let len := if ncu = 0 then 0 else
    let hasLf := s.bytes.getD (ncu - 1) 0 == 0x0a
    let twoBytes := ncu > 1
    let hasCr := hasLf && twoBytes && s.bytes.getD (ncu - (if twoBytes then 1 else 0) - 1) 0 == 0x0d
    ncu - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)
  ⟨s.bytes.take len, s.address⟩
def ChompProperty : Prop := ∀ s, (chomp s).bytes =
  let ncu := s.bytes.length
  let len := if ncu = 0 then 0 else
    let hasLf := s.bytes.getD (ncu - 1) 0 == 0x0a
    let twoBytes := ncu > 1
    let hasCr := hasLf && twoBytes && s.bytes.getD (ncu - (if twoBytes then 1 else 0) - 1) 0 == 0x0d
    ncu - (if hasLf then 1 else 0) - (if hasCr then 1 else 0)
  s.bytes.take len
theorem chomp_proven : ChompProperty := by unfold ChompProperty; intros; rfl

def replace (replaceImpl : View → List α → Int → β) (s : View) (pairs : List α) (count : Int) :=
  replaceImpl s pairs count
def ReplaceProperty : Prop := ∀ (α β : Type) (impl : View → List α → Int → β) s pairs count,
  replace impl s pairs count = impl s pairs count
theorem replace_proven : ReplaceProperty := by unfold ReplaceProperty; intros; rfl

end JuliaLean.StringsCovA.StringViewFaithful
