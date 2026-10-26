import JuliaLean.Strings

namespace JuliaLean.StringsCovA.SubstringFaithfulAccess

open JuliaLean JuliaLean.Strings

def ncodeunitsM (s : JSub) := s.ncu
def NcodeunitsProperty : Prop := ∀ s, ncodeunitsM s = s.ncu
theorem ncodeunits_proven : NcodeunitsProperty := by unfold NcodeunitsProperty; intros; rfl

def codeunitType (codeunitParent : JStr → Nat) (s : JSub) := codeunitParent s.str
def CodeunitTypeProperty : Prop := ∀ f s, codeunitType f s = f s.str
theorem codeunitType_proven : CodeunitTypeProperty := by unfold CodeunitTypeProperty; intros; rfl

def lengthGeneric (lengthParent : JStr → JInt64 → JInt64 → SJl JInt64) (s : JSub) :=
  lengthParent s.str (s.offset + ix 1) (s.offset + s.ncu)
def LengthGenericProperty : Prop := ∀ f s, lengthGeneric f s = f s.str (s.offset + ix 1) (s.offset + s.ncu)
theorem lengthGeneric_proven : LengthGenericProperty := by unfold LengthGenericProperty; intros; rfl

def lengthString (lengthParent : JStr → JInt64 → JInt64 → SJl JInt64) (s : JSub) :=
  lengthParent s.str (s.offset + ix 1) (s.offset + s.ncu)
def LengthStringProperty : Prop := ∀ f s, lengthString f s = f s.str (s.offset + ix 1) (s.offset + s.ncu)
theorem lengthString_proven : LengthStringProperty := by unfold LengthStringProperty; intros; rfl

def codeunitAt (codeunitParent : JStr → JInt64 → SJl UInt8) (s : JSub) (i : JInt64) : SJl UInt8 :=
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else codeunitParent s.str (s.offset + i)
def CodeunitAtProperty : Prop := ∀ f s i, codeunitAt f s i =
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else f s.str (s.offset + i)
theorem codeunitAt_proven : CodeunitAtProperty := by unfold CodeunitAtProperty; intros; rfl

def getindexAt (getParent : JStr → JInt64 → SJl UInt32) (s : JSub) (i : JInt64) : SJl UInt32 :=
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else getParent s.str (s.offset + i)
def GetindexAtProperty : Prop := ∀ f s i, getindexAt f s i =
  if i.val < 1 || i.val > s.ncu.val then .error boundsErr else f s.str (s.offset + i)
theorem getindexAt_proven : GetindexAtProperty := by unfold GetindexAtProperty; intros; rfl

def isasciiM (asciiBytes : List UInt8 → Bool) (s : JSub) := asciiBytes s.view.bytes
def IsasciiProperty : Prop := ∀ f s, isasciiM f s = f s.view.bytes
theorem isascii_proven : IsasciiProperty := by unfold IsasciiProperty; intros; rfl

def isvalidM (check : JSub → JInt64 → Bool) (parentValid : JStr → JInt64 → Bool) (s : JSub) (i : JInt64) :=
  check s i && parentValid s.str (s.offset + i)
def IsvalidProperty : Prop := ∀ cb pv s i, isvalidM cb pv s i = (cb s i && pv s.str (s.offset + i))
theorem isvalid_proven : IsvalidProperty := by unfold IsvalidProperty; intros; rfl

def thisindM (helper : JSub → JInt64 → SJl JInt64) (s : JSub) (i : JInt64) := helper s i
def ThisindProperty : Prop := ∀ f s i, thisindM f s i = f s i
theorem thisind_proven : ThisindProperty := by unfold ThisindProperty; intros; rfl

def nextindM (helper : JSub → JInt64 → SJl JInt64) (s : JSub) (i : JInt64) := helper s i
def NextindProperty : Prop := ∀ f s i, nextindM f s i = f s i
theorem nextind_proven : NextindProperty := by unfold NextindProperty; intros; rfl

def lastindexM (thisind : JSub → JInt64 → JInt64) (s : JSub) := thisind s s.ncu
def LastindexProperty : Prop := ∀ f s, lastindexM f s = f s s.ncu
theorem lastindex_proven : LastindexProperty := by unfold LastindexProperty; intros; rfl

def parentM (s : JSub) := s.str
def ParentProperty : Prop := ∀ s, parentM s = s.str
theorem parent_proven : ParentProperty := by unfold ParentProperty; intros; rfl

def parentindicesM (thisind : JStr → JInt64 → JInt64) (s : JSub) :=
  (s.offset + ix 1, thisind s.str (s.offset + s.ncu))
def ParentindicesProperty : Prop := ∀ f s, parentindicesM f s = (s.offset + ix 1, f s.str (s.offset + s.ncu))
theorem parentindices_proven : ParentindicesProperty := by unfold ParentindicesProperty; intros; rfl

def eqM (memcmp : JSub → JSub → Int) (a b : JSub) : Bool :=
  a.ncu.val == b.ncu.val && memcmp a b == 0
def EqProperty : Prop := ∀ memcmp a b, eqM memcmp a b = (a.ncu.val == b.ncu.val && memcmp a b == 0)
theorem eq_proven : EqProperty := by unfold EqProperty; intros; rfl

def cmpM (memcmp : JSub → JSub → Int) (a b : JSub) : Int :=
  let c := memcmp a b
  if c < 0 then -1 else if c > 0 then 1 else Int.sign (a.ncu.val - b.ncu.val)
def CmpProperty : Prop := ∀ memcmp a b, cmpM memcmp a b =
  let c := memcmp a b; if c < 0 then -1 else if c > 0 then 1 else Int.sign (a.ncu.val - b.ncu.val)
theorem cmp_proven : CmpProperty := by unfold CmpProperty; intros; rfl

def cconvertU8 (s : JSub) := s
def CconvertU8Property : Prop := ∀ s, cconvertU8 s = s
theorem cconvertU8_proven : CconvertU8Property := by unfold CconvertU8Property; intros; rfl

def cconvertI8 (s : JSub) := s
def CconvertI8Property : Prop := ∀ s, cconvertI8 s = s
theorem cconvertI8_proven : CconvertI8Property := by unfold CconvertI8Property; intros; rfl

def unsafeConvert (convert : Nat → Nat) (base : Nat) (s : JSub) := convert base + s.offset.val
def UnsafeConvertProperty : Prop := ∀ convert base s, unsafeConvert convert base s = convert base + s.offset.val
theorem unsafeConvert_proven : UnsafeConvertProperty := by unfold UnsafeConvertProperty; intros; rfl

def pointerM (base : Nat) (s : JSub) := base + s.offset.val.toNat
def PointerProperty : Prop := ∀ base s, pointerM base s = base + s.offset.val.toNat
theorem pointer_proven : PointerProperty := by unfold PointerProperty; intros; rfl

def pointerAtM (base : Int) (s : JSub) (i : Int) := base + s.offset.val + i - 1
def PointerAtProperty : Prop := ∀ base s i, pointerAtM base s i = base + s.offset.val + i - 1
theorem pointerAt_proven : PointerAtProperty := by unfold PointerAtProperty; intros; rfl

def hashM (hashBytes : Nat → Nat → UInt64 → UInt64 → UInt64) (base : Nat)
    (s : JSub) (h secret : UInt64) := hashBytes (base + s.offset.val.toNat) s.ncu.val.toNat h secret
def HashProperty : Prop := ∀ hb base s h secret,
  hashM hb base s h secret = hb (base + s.offset.val.toNat) s.ncu.val.toNat h secret
theorem hash_proven : HashProperty := by unfold HashProperty; intros; rfl

def isannotatedM (f : JStr → Bool) (s : JSub) := f s.str
def IsannotatedProperty : Prop := ∀ f s, isannotatedM f s = f s.str
theorem isannotated_proven : IsannotatedProperty := by unfold IsannotatedProperty; intros; rfl

def stringString (s : JStr) := s
def StringStringProperty : Prop := ∀ s, stringString s = s
theorem stringString_proven : StringStringProperty := by unfold StringStringProperty; intros; rfl

def stringSub (toString : JSub → JStr) (s : JSub) := toString s
def StringSubProperty : Prop := ∀ f s, stringSub f s = f s
theorem stringSub_proven : StringSubProperty := by unfold StringSubProperty; intros; rfl

def symbolM (ccall : Nat → Nat → Nat) (base : Nat) (s : JSub) :=
  ccall (base + s.offset.val.toNat) s.ncu.val.toNat
def SymbolProperty : Prop := ∀ ccall base s,
  symbolM ccall base s = ccall (base + s.offset.val.toNat) s.ncu.val.toNat
theorem symbol_proven : SymbolProperty := by unfold SymbolProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringFaithfulAccess
