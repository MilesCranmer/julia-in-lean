import JuliaLean.base.strings.substring
import JuliaLean.Proofs.base.strings.string.entries

namespace JuliaLean.StringsCovA.SubstringFaithfulFinal

open JuliaLean JuliaLean.Strings

def WriteCharProperty : Prop := ∀ out c offs, writeChar out c offs =
  let x := bswap32 c
  let n := ncodeunitsChar c
  let out := storeByte out offs x.toUInt8
  if n = 1 then (out, n) else
  let x := x >>> (8 : UInt32)
  let out := storeByte out (offs + 1) x.toUInt8
  if n = 2 then (out, n) else
  let x := x >>> (8 : UInt32)
  let out := storeByte out (offs + 2) x.toUInt8
  if n = 3 then (out, n) else
  let x := x >>> (8 : UInt32)
  (storeByte out (offs + 3) x.toUInt8, n)
theorem writeChar_proven : WriteCharProperty := by unfold WriteCharProperty; intros; rfl
def WriteStringProperty : Prop := ∀ out source offs,
  writeString out source offs = (Strings.writeAt out (offs - 1) source, source.length)
theorem writeString_proven : WriteStringProperty := by unfold WriteStringProperty; intros; rfl
def WriteSubStringProperty : Prop := ∀ out source offs,
  writeSubString out source offs =
    (Strings.writeAt out (offs - 1) source.view.bytes, source.view.bytes.length)
theorem writeSubString_proven : WriteSubStringProperty := by unfold WriteSubStringProperty; intros; rfl
def WriteSymbolProperty : Prop := ∀ out source offs,
  writeSymbol out source offs = (Strings.writeAt out (offs - 1) source, source.length)
theorem writeSymbol_proven : WriteSymbolProperty := by unfold WriteSymbolProperty; intros; rfl

def BuildStringProperty : Prop := ∀ values, buildString values =
  let n := (values.map valueSize).sum
  if n < 2 ^ 62 then .ok (writeValues values (List.replicate n 0) 1)
  else .error .outOfMemory
theorem buildString_proven : BuildStringProperty := by unfold BuildStringProperty; intros; rfl
def StringRestrictedProperty : Prop := ∀ values, stringRestricted values = buildString values
theorem stringRestricted_proven : StringRestrictedProperty := by unfold StringRestrictedProperty; intros; rfl
def StringAllProperty : Prop := ∀ values, stringAll values = buildString values
theorem stringAll_proven : StringAllProperty := by unfold StringAllProperty; intros; rfl
def RepeatBitIntegerProperty : Prop := ∀ s r, repeatBitInteger s r = Strings.repeatStr s r
theorem repeatBitInteger_proven : RepeatBitIntegerProperty := by unfold RepeatBitIntegerProperty; intros; rfl
def RepeatIntegerProperty : Prop := ∀ s r, repeatInteger s r = Strings.repeatStr s r
theorem repeatInteger_proven : RepeatIntegerProperty := by unfold RepeatIntegerProperty; intros; rfl
def FilterStringProperty : Prop := ∀ f s,
  filterString f s = stringOfChars ((Strings.chars s).filter f)
theorem filterString_proven : FilterStringProperty := by unfold FilterStringProperty; intros; rfl
def GetindexRangeProperty : Prop := ∀ s i j, getindexRange s i j = Strings.substring s i j
theorem getindexRange_proven : GetindexRangeProperty := by unfold GetindexRangeProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringFaithfulFinal
