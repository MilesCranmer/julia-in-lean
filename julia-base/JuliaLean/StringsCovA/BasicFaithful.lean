import JuliaLean.StringsCovA.Basic

namespace JuliaLean.StringsCovA.BasicFaithful

open JuliaLean JuliaLean.Strings

def CodeunitIntegerProperty : Prop := ∀ (α : Type) isInt (dispatch : Int → SJl α) i,
  Basic.integerFallback isInt dispatch i = if isInt then .error (.jl (.methodError "missing Int method")) else dispatch i
theorem codeunitInteger_proven : CodeunitIntegerProperty := by unfold CodeunitIntegerProperty; intros; rfl

def IsvalidIntegerProperty : Prop := ∀ (α : Type) isInt (dispatch : Int → SJl α) i,
  Basic.integerFallback isInt dispatch i = if isInt then .error (.jl (.methodError "missing Int method")) else dispatch i
theorem isvalidInteger_proven : IsvalidIntegerProperty := by unfold IsvalidIntegerProperty; intros; rfl

def IterateIntegerProperty : Prop := ∀ (α : Type) isInt (dispatch : Int → SJl α) i,
  Basic.integerFallback isInt dispatch i = if isInt then .error (.jl (.methodError "missing Int method")) else dispatch i
theorem iterateInteger_proven : IterateIntegerProperty := by unfold IterateIntegerProperty; intros; rfl

def EltypeProperty : Prop := ∀ _u : Unit, Basic.eltypeString = "Char"
theorem eltype_proven : EltypeProperty := by unfold EltypeProperty; intros; rfl

def SizeofProperty : Prop := ∀ n unitBytes, Basic.sizeof n unitBytes = n * unitBytes
theorem sizeof_proven : SizeofProperty := by unfold SizeofProperty; intros; rfl

def FirstindexProperty : Prop := ∀ _u : Unit, Basic.firstindex = 1
theorem firstindex_proven : FirstindexProperty := by unfold FirstindexProperty; intros; rfl

def LastindexProperty : Prop := ∀ this n, Basic.lastindex this n = this n
theorem lastindex_proven : LastindexProperty := by unfold LastindexProperty; intros; rfl

def IsEmptyProperty : Prop := ∀ n, Basic.isempty n = (n == 0)
theorem isempty_proven : IsEmptyProperty := by unfold IsEmptyProperty; intros; rfl

def FirstProperty : Prop := ∀ (α : Type) (get : Int → SJl α), Basic.first get = get 1
theorem first_proven : FirstProperty := by unfold FirstProperty; intros; rfl

def GetindexProperty : Prop :=
  (∀ (α : Type) inb valid (iter : Int → α) i, Basic.getindex inb valid iter i =
    if !inb i then .error (.jl .boundsError) else if valid i then .ok (iter i) else .error (.stringIndexError i)) ∧
  (∀ (α : Type) (s : α), Basic.getindexColon s = s) ∧
  (∀ (α : Type) get is, Basic.getindexVector (α := α) get is = is.map get) ∧
  Basic.getindexBool = .error (.jl (.argumentError "logical indexing not supported for strings"))
theorem getindex_proven : GetindexProperty := by
  unfold GetindexProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def GetProperty : Prop := ∀ (α : Type) inb get i (d : α),
  Basic.getDefault inb get i d = if inb i then get i else d
theorem get_proven : GetProperty := by unfold GetProperty; intros; rfl

def CheckboundsProperty : Prop :=
  (∀ n i, Basic.checkboundsIndex n i = decide (1 ≤ i ∧ i ≤ n)) ∧
  (∀ n lo hi, Basic.checkboundsRange n lo hi = (hi < lo || decide (1 ≤ lo ∧ hi ≤ n))) ∧
  (∀ check is, Basic.checkboundsAll check is = is.all check) ∧
  (∀ check is, Basic.checkboundsAll check is = is.all check) ∧
  (∀ ok, Basic.checkboundsThrow ok = if ok then .ok () else .error .boundsError)
theorem checkbounds_proven : CheckboundsProperty := by
  unfold CheckboundsProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def StringProperty : Prop := Basic.stringEmpty = [] ∧ ∀ (α : Type) (s : α), Basic.stringIdentity s = s
theorem string_proven : StringProperty := by constructor <;> intros <;> rfl

def VectorProperty : Prop :=
  (∀ (α : Type) toString (s : α), Basic.vectorBytes toString s = toString s) ∧
  (∀ (α : Type) toString (s : α), Basic.vectorBytes toString s = toString s) ∧
  (∀ (α β : Type) collect (s : α), Basic.vectorChars (β := β) collect s = collect s)
theorem vector_proven : VectorProperty := by
  unfold VectorProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def SymbolProperty : Prop :=
  (∀ (α : Type) intern toString (s : α), Basic.symbolString intern toString s = intern (toString s)) ∧
  (∀ (α : Type) render intern (xs : List α), Basic.symbolArgs render intern xs = intern (render xs))
theorem symbol_proven : SymbolProperty := by constructor <;> intros <;> rfl

def ConvertProperty : Prop :=
  (∀ (α : Type) (s : α), Basic.convertIdentity s = s) ∧
  (∀ (α β : Type) ctor (s : α), Basic.convertString (β := β) ctor s = ctor s)
theorem convert_proven : ConvertProperty := by constructor <;> intros <;> rfl

def SummaryProperty : Prop := ∀ n t, Basic.summary n t =
  (if n = 0 then "empty" else toString n ++ "-codeunit") ++ " " ++ t
theorem summary_proven : SummaryProperty := by unfold SummaryProperty; intros; rfl

def ConcatProperty : Prop := ∀ (α β : Type) ann plain annotatedJoin (xs : List α),
  Basic.concat (β := β) ann plain annotatedJoin xs = if ann then annotatedJoin xs else plain xs
theorem concat_proven : ConcatProperty := by unfold ConcatProperty; intros; rfl

def OneProperty : Prop := ∀ (α : Type) (empty : α), Basic.oneString empty = empty
theorem one_proven : OneProperty := by unfold OneProperty; intros; rfl

def IsannotatedProperty : Prop :=
  (∀ b s c, Basic.isannotatedType b s c = (!b && (s || c))) ∧
  (∀ (α : Type) f (x : α), Basic.isannotatedValue f x = f x)
theorem isannotated_proven : IsannotatedProperty := by constructor <;> intros <;> rfl

def CmpStringProperty : Prop := ∀ a b, Basic.cmpString a b = Strings.cmpGeneric a b
theorem cmpString_proven : CmpStringProperty := by unfold CmpStringProperty; intros; rfl
def EqStringProperty : Prop := ∀ a b, Basic.eqString a b = (Strings.cmpGeneric a b == 0)
theorem eqString_proven : EqStringProperty := by unfold EqStringProperty; intros; rfl
def IslessStringProperty : Prop := ∀ a b, Basic.islessString a b = decide (Strings.cmpGeneric a b < 0)
theorem islessString_proven : IslessStringProperty := by unfold IslessStringProperty; intros; rfl
def CmpSymbolProperty : Prop := ∀ strcmp a b, Basic.cmpSymbol strcmp a b = Int.sign (strcmp a b)
theorem cmpSymbol_proven : CmpSymbolProperty := by unfold CmpSymbolProperty; intros; rfl
def IslessSymbolProperty : Prop := ∀ strcmp a b,
  Basic.islessSymbol strcmp a b = decide (Int.sign (strcmp a b) < 0)
theorem islessSymbol_proven : IslessSymbolProperty := by unfold IslessSymbolProperty; intros; rfl

def LengthProperty : Prop :=
  (∀ s, Basic.lengthString s = Strings.length s) ∧
  (∀ s i j, Basic.lengthBetween s i j = Strings.lengthRange s i j) ∧
  (∀ s i j, Basic.lengthBetween s i j = Strings.lengthRange s i j)
theorem length_proven : LengthProperty := by
  unfold LengthProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def ThisindProperty : Prop :=
  (∀ s i, Basic.thisindInteger s i = Strings.thisind s i) ∧
  (∀ s i, Basic.thisindInteger s i = Strings.thisind s i)
theorem thisind_proven : ThisindProperty := by constructor <;> intros <;> rfl

def PrevindProperty : Prop :=
  (∀ s i n, Basic.previndInteger s i n = Strings.previndN s i n) ∧
  (∀ s i, Basic.previndOne s i = Strings.prevind s i) ∧
  (∀ s i, Basic.previndOne s i = Strings.prevind s i) ∧
  (∀ s i n, Basic.previndInteger s i n = Strings.previndN s i n)
theorem prevind_proven : PrevindProperty := by
  unfold PrevindProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def NextindWrappersProperty : Prop :=
  (∀ s i n, Basic.nextindInteger s i n = Strings.nextindN s i n) ∧
  (∀ s i, Basic.nextindOne s i = Strings.nextind s i) ∧
  (∀ s i, Basic.nextindOne s i = Strings.nextind s i)
theorem nextindWrappers_proven : NextindWrappersProperty := by
  unfold NextindWrappersProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def EachIndexProperty : Prop :=
  (∀ s, Basic.keys s = ⟨s⟩) ∧
  (∀ e, Basic.eachLength e = Strings.length e.s) ∧
  (∀ e, Basic.eachFirst e = ix 1) ∧
  (∀ e, Basic.eachLast e = Strings.lastindex e.s) ∧
  (∀ e st, Basic.eachIterate e st = if st.val > (Strings.ncodeunits e.s).val then none else
    match Strings.nextind e.s st with | .ok n => some (st, n) | .error _ => none) ∧
  ∀ _u : Unit, Basic.eachEltype = "Int"
theorem eachIndex_proven : EachIndexProperty := by
  unfold EachIndexProperty
  repeat' apply And.intro
  all_goals intros <;> rfl

def IsasciiCharProperty : Prop := ∀ c, Strings.isasciiChar c = decide (bswap32 c < 0x80)
theorem isasciiChar_proven : IsasciiCharProperty := by unfold IsasciiCharProperty; intros; rfl
def IsasciiStringProperty : Prop := ∀ s, Basic.isasciiString s = Strings.isascii s
theorem isasciiString_proven : IsasciiStringProperty := by unfold IsasciiStringProperty; intros; rfl
def IsasciiAbstractCharProperty : Prop := ∀ c, Basic.isasciiChar c = decide (c < 0x80)
theorem isasciiAbstractChar_proven : IsasciiAbstractCharProperty := by unfold IsasciiAbstractCharProperty; intros; rfl
def IsasciiRangeProperty : Prop := ∀ bytes first last,
  Basic.isasciiRange bytes first last = Strings.isasciiRange bytes first last
theorem isasciiRange_proven : IsasciiRangeProperty := by unfold IsasciiRangeProperty; intros; rfl
def IsasciiChunksProperty : Prop := ∀ chunk bytes first last,
  Basic.isasciiChunks chunk bytes first last = Strings.isasciiChunksLoop chunk bytes last bytes.length first
theorem isasciiChunks_proven : IsasciiChunksProperty := by unfold IsasciiChunksProperty; intros; rfl
def IsasciiVectorProperty : Prop := ∀ bytes, Basic.isasciiVector bytes = bytes.all (· < 0x80)
theorem isasciiVector_proven : IsasciiVectorProperty := by unfold IsasciiVectorProperty; intros; rfl

def MapProperty : Prop := ∀ f s, Basic.mapString f s = stringOfChars ((Strings.chars s).map f)
theorem map_proven : MapProperty := by unfold MapProperty; intros; rfl
def FilterProperty : Prop := ∀ f s, Basic.filterString f s = stringOfChars ((Strings.chars s).filter f)
theorem filter_proven : FilterProperty := by unfold FilterProperty; intros; rfl
def LastNProperty : Prop := ∀ s n, Basic.lastN s n = Strings.lastN s n
theorem lastN_proven : LastNProperty := by unfold LastNProperty; intros; rfl
def ReverseindProperty : Prop := ∀ this n i, Basic.reverseind this n i = this (n - i + 1)
theorem reverseind_proven : ReverseindProperty := by unfold ReverseindProperty; intros; rfl
def RepeatProperty : Prop := ∀ (α : Type) toString (s : α) r,
  Basic.repeatString toString s r = Strings.repeatStr (toString s) r
theorem repeat_proven : RepeatProperty := by unfold RepeatProperty; intros; rfl
def PowerProperty : Prop := ∀ (α β : Type) repeatFn (s : α) r,
  Basic.powerString (β := β) repeatFn s r = repeatFn s r
theorem power_proven : PowerProperty := by unfold PowerProperty; intros; rfl
def ReverseIterateProperty : Prop := ∀ (α : Type) first get prev (i : Int),
  Basic.reverseIterate (α := α) first get prev i = if i < 1 then none else some (get i, prev i)
theorem reverseIterate_proven : ReverseIterateProperty := by unfold ReverseIterateProperty; intros; rfl

def CodeUnitsCtorProperty : Prop := ∀ bytes, Basic.codeUnitsCtor bytes = ⟨bytes⟩
theorem codeUnitsCtor_proven : CodeUnitsCtorProperty := by unfold CodeUnitsCtorProperty; intros; rfl
def CuSizeofProperty : Prop := ∀ s, Basic.cuSizeof s = s.bytes.length
theorem cuSizeof_proven : CuSizeofProperty := by unfold CuSizeofProperty; intros; rfl
def CuSizeProperty : Prop := ∀ s, Basic.cuSize s = (s.bytes.length, ())
theorem cuSize_proven : CuSizeProperty := by unfold CuSizeProperty; intros; rfl
def CuElsizeProperty : Prop := ∀ _u : Unit, Basic.cuElsize = 1
theorem cuElsize_proven : CuElsizeProperty := by unfold CuElsizeProperty; intros; rfl
def CuGetindexProperty : Prop := ∀ s i, Basic.cuGetindex s i = s.bytes.getD (i - 1) 0
theorem cuGetindex_proven : CuGetindexProperty := by unfold CuGetindexProperty; intros; rfl
def CuIndexStyleProperty : Prop := ∀ _u : Unit, Basic.cuIndexStyle = "IndexLinear"
theorem cuIndexStyle_proven : CuIndexStyleProperty := by unfold CuIndexStyleProperty; intros; rfl
def CuCheckboundsProperty : Prop := ∀ s i,
  Basic.cuCheckbounds s i = decide (1 ≤ i ∧ i ≤ s.bytes.length)
theorem cuCheckbounds_proven : CuCheckboundsProperty := by unfold CuCheckboundsProperty; intros; rfl
def CuDataidsProperty : Prop := ∀ id s, Basic.cuDataids id s = id s.bytes
theorem cuDataids_proven : CuDataidsProperty := by unfold CuDataidsProperty; intros; rfl
def CuWriteProperty : Prop := ∀ write s, Basic.cuWrite write s = write s.bytes
theorem cuWrite_proven : CuWriteProperty := by unfold CuWriteProperty; intros; rfl
def CuCconvertProperty : Prop := ∀ convert s, Basic.cuCconvert convert s = convert s.bytes
theorem cuCconvert_proven : CuCconvertProperty := by unfold CuCconvertProperty; intros; rfl
def CuSimilarProperty : Prop := ∀ make n, Basic.cuSimilar make n = make n
theorem cuSimilar_proven : CuSimilarProperty := by unfold CuSimilarProperty; intros; rfl
def CodeunitsProperty : Prop := ∀ bytes, Basic.codeunits bytes = ⟨bytes⟩
theorem codeunits_proven : CodeunitsProperty := by unfold CodeunitsProperty; intros; rfl
def SplitRestProperty : Prop := ∀ split s n, Basic.splitRest split s n = split s n
theorem splitRest_proven : SplitRestProperty := by unfold SplitRestProperty; intros; rfl

end JuliaLean.StringsCovA.BasicFaithful
