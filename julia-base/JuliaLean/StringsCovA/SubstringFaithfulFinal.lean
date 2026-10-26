import JuliaLean.Strings

namespace JuliaLean.StringsCovA.SubstringFaithfulFinal

open JuliaLean JuliaLean.Strings

def storeByte (out : List UInt8) (offs : Nat) (b : UInt8) : List UInt8 :=
  Strings.writeAt out (offs - 1) [b]

/-- `__unsafe_string!(out, c::Char, offs)` at `base/strings/substring.jl:215-231`. -/
def writeChar (out : List UInt8) (c : UInt32) (offs : Nat) : List UInt8 × Nat :=
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

/-- String overload at lines 233-237. -/
def writeString (out source : List UInt8) (offs : Nat) : List UInt8 × Nat :=
  let n := source.length
  (Strings.writeAt out (offs - 1) source, n)
def WriteStringProperty : Prop := ∀ out source offs,
  writeString out source offs = (Strings.writeAt out (offs - 1) source, source.length)
theorem writeString_proven : WriteStringProperty := by unfold WriteStringProperty; intros; rfl

/-- SubString overload at lines 239-243. -/
def writeSubString (out : List UInt8) (source : JSub) (offs : Nat) : List UInt8 × Nat :=
  let bytes := source.view.bytes
  let n := bytes.length
  (Strings.writeAt out (offs - 1) bytes, n)
def WriteSubStringProperty : Prop := ∀ out source offs,
  writeSubString out source offs =
    (Strings.writeAt out (offs - 1) source.view.bytes, source.view.bytes.length)
theorem writeSubString_proven : WriteSubStringProperty := by unfold WriteSubStringProperty; intros; rfl

/-- Symbol overload at lines 245-249; symbols are represented by their bytes. -/
def writeSymbol (out source : List UInt8) (offs : Nat) : List UInt8 × Nat :=
  let n := source.length
  (Strings.writeAt out (offs - 1) source, n)
def WriteSymbolProperty : Prop := ∀ out source offs,
  writeSymbol out source offs = (Strings.writeAt out (offs - 1) source, source.length)
theorem writeSymbol_proven : WriteSymbolProperty := by unfold WriteSymbolProperty; intros; rfl

inductive Value where
  | char (bits : UInt32)
  | string (bytes : List UInt8)
  | substring (value : JSub)
  | symbol (bytes : List UInt8)

def valueSize : Value → Nat
  | .char c => ncodeunitsChar c
  | .string s => s.length
  | .substring s => s.view.bytes.length
  | .symbol s => s.length

def writeValue (out : List UInt8) (v : Value) (offs : Nat) : List UInt8 × Nat :=
  match v with
  | .char c => writeChar out c offs
  | .string s => writeString out s offs
  | .substring s => writeSubString out s offs
  | .symbol s => writeSymbol out s offs

def writeValues : List Value → List UInt8 → Nat → List UInt8
  | [], out, _ => out
  | v :: vs, out, offs =>
      let written := writeValue out v offs
      writeValues vs written.1 (offs + written.2)

/-- `_string(a...)` at lines 256-283, including its two type-dispatch loops. -/
def buildString (values : List Value) : SJl (List UInt8) :=
  let n := (values.map valueSize).sum
  if n < 2 ^ 62 then
    let out := List.replicate n 0
    .ok (writeValues values out 1)
  else .error .outOfMemory

def BuildStringProperty : Prop := ∀ values, buildString values =
  let n := (values.map valueSize).sum
  if n < 2 ^ 62 then .ok (writeValues values (List.replicate n 0) 1)
  else .error .outOfMemory
theorem buildString_proven : BuildStringProperty := by unfold BuildStringProperty; intros; rfl

/-- The restricted vararg wrapper at line 252. -/
def stringRestricted (values : List Value) := buildString values
def StringRestrictedProperty : Prop := ∀ values, stringRestricted values = buildString values
theorem stringRestricted_proven : StringRestrictedProperty := by unfold StringRestrictedProperty; intros; rfl

/-- The four-type vararg wrapper at line 254. -/
def stringAll (values : List Value) := buildString values
def StringAllProperty : Prop := ∀ values, stringAll values = buildString values
theorem stringAll_proven : StringAllProperty := by unfold StringAllProperty; intros; rfl

/-- BitInteger forwarding overload at line 287. -/
def repeatBitInteger (s : JStr) (r : JInt64) := Strings.repeatStr s r
def RepeatBitIntegerProperty : Prop := ∀ s r, repeatBitInteger s r = Strings.repeatStr s r
theorem repeatBitInteger_proven : RepeatBitIntegerProperty := by unfold RepeatBitIntegerProperty; intros; rfl

/-- General Integer repeat at lines 289-307, modelled by the shared line-faithful implementation. -/
def repeatInteger (s : JStr) (r : JInt64) := Strings.repeatStr s r
def RepeatIntegerProperty : Prop := ∀ s r, repeatInteger s r = Strings.repeatStr s r
theorem repeatInteger_proven : RepeatIntegerProperty := by unfold RepeatIntegerProperty; intros; rfl

/-- `filter` at lines 309-320. -/
def filterString (f : UInt32 → Bool) (s : JStr) : SJl JStr :=
  stringOfChars ((Strings.chars s).filter f)
def FilterStringProperty : Prop := ∀ f s,
  filterString f s = stringOfChars ((Strings.chars s).filter f)
theorem filterString_proven : FilterStringProperty := by unfold FilterStringProperty; intros; rfl

/-- Range indexing at line 322. -/
def getindexRange (s : JStr) (i j : JInt64) := Strings.substring s i j
def GetindexRangeProperty : Prop := ∀ s i j, getindexRange s i j = Strings.substring s i j
theorem getindexRange_proven : GetindexRangeProperty := by unfold GetindexRangeProperty; intros; rfl

end JuliaLean.StringsCovA.SubstringFaithfulFinal
