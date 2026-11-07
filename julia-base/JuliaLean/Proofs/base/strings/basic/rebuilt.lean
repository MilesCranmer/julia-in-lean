import JuliaLean.base.strings.basic
import JuliaLean.Proofs.base.strings.basic.coverage

/-!
Faithful per-method models for rows rejected by the fixed review of
`base/strings/basic.jl` at Julia `bbfa0ce4150`.

An `IntegerInput` or `AbstractStringInput` records the observable dispatches
provided by an arbitrary Julia value.  This keeps conversion failures and
custom `AbstractString` behavior explicit instead of assuming `String`.
-/

namespace JuliaLean.StringsCovA.BasicRebuilt

open JuliaLean JuliaLean.Strings

@[simp] private theorem exceptOkBind (value : α) (next : α → Except ε β) :
    (Except.ok value : Except ε α).bind next = next value := rfl

@[simp] private theorem exceptErrorBind (error : ε) (next : α → Except ε β) :
    (Except.error error : Except ε α).bind next = .error error := rfl

def CodeunitIntegerProperty : Prop :=
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch,
    i.isMachineInt = true →
    codeunitInteger s i (dispatch : S → Int → SJl C) =
      .error (.jl (.methodError "codeunit(::AbstractString, ::Int) missing"))) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch error,
    i.isMachineInt = false → i.toInt = .error error →
    codeunitInteger s i (dispatch : S → Int → SJl C) = .error error) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch converted,
    i.isMachineInt = false → i.toInt = .ok converted →
    codeunitInteger s i (dispatch : S → Int → SJl C) = dispatch s converted)

theorem codeunitInteger_proven : CodeunitIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [codeunitInteger, bind, Except.bind, pure, Except.pure]

def IsvalidIntegerProperty : Prop :=
  (∀ (S I : Type) (s : S) (i : IntegerInput I) dispatch,
    i.isMachineInt = true →
    isvalidInteger s i (dispatch : S → Int → SJl Bool) =
      .error (.jl (.methodError "isvalid(::AbstractString, ::Int) missing"))) ∧
  (∀ (S I : Type) (s : S) (i : IntegerInput I) dispatch error,
    i.isMachineInt = false → i.toInt = .error error →
    isvalidInteger s i (dispatch : S → Int → SJl Bool) = .error error) ∧
  (∀ (S I : Type) (s : S) (i : IntegerInput I) dispatch converted,
    i.isMachineInt = false → i.toInt = .ok converted →
    isvalidInteger s i (dispatch : S → Int → SJl Bool) = dispatch s converted)

theorem isvalidInteger_proven : IsvalidIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [isvalidInteger, bind, Except.bind, pure, Except.pure]

def IterateIntegerProperty : Prop :=
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch,
    i.isMachineInt = true →
    iterateInteger s i (dispatch : S → Int → SJl (Option (C × Int))) =
      .error (.jl (.methodError "iterate(::AbstractString, ::Int) missing"))) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch error,
    i.isMachineInt = false → i.toInt = .error error →
    iterateInteger s i (dispatch : S → Int → SJl (Option (C × Int))) = .error error) ∧
  (∀ (S I C : Type) (s : S) (i : IntegerInput I) dispatch converted,
    i.isMachineInt = false → i.toInt = .ok converted →
    iterateInteger s i (dispatch : S → Int → SJl (Option (C × Int))) = dispatch s converted)

theorem iterateInteger_proven : IterateIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [iterateInteger, bind, Except.bind, pure, Except.pure]

def SizeofProperty : Prop :=
  (∀ (S : Type) (s : AbstractStringInput S) count unitSize,
    s.ncodeunits = .ok count → s.codeunitSize = .ok unitSize →
    sizeofString s = .ok (count * unitSize)) ∧
  (∀ (S : Type) (s : AbstractStringInput S) error,
    s.ncodeunits = .error error → sizeofString s = .error error) ∧
  (∀ (S : Type) (s : AbstractStringInput S) count error,
    s.ncodeunits = .ok count → s.codeunitSize = .error error →
    sizeofString s = .error error)

theorem sizeof_proven : SizeofProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [sizeofString, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def LastindexProperty : Prop :=
  (∀ (S : Type) (s : AbstractStringInput S) thisind count,
    s.ncodeunits = .ok count →
    lastindexString s thisind = thisind s.value count) ∧
  (∀ (S : Type) (s : AbstractStringInput S) thisind error,
    s.ncodeunits = .error error →
    lastindexString s thisind = .error error)

theorem lastindex_proven : LastindexProperty := by
  constructor <;> intros <;>
    simp_all [lastindexString, bind, Except.bind, pure, Except.pure]

def IsEmptyProperty : Prop :=
  (∀ (S : Type) (s : AbstractStringInput S) count,
    s.ncodeunits = .ok count → isemptyString s = .ok (count == 0)) ∧
  (∀ (S : Type) (s : AbstractStringInput S) error,
    s.ncodeunits = .error error → isemptyString s = .error error)

theorem isempty_proven : IsEmptyProperty := by
  constructor <;> intros <;>
    simp_all [isemptyString, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def FirstProperty : Prop :=
  (∀ (S C : Type) (s : AbstractStringInput S) getindex index,
    s.firstindex = .ok index →
    firstString s (getindex : S → Int → SJl C) = getindex s.value index) ∧
  (∀ (S C : Type) (s : AbstractStringInput S) getindex error,
    s.firstindex = .error error →
    firstString s (getindex : S → Int → SJl C) = .error error)

theorem first_proven : FirstProperty := by
  constructor <;> intros <;>
    simp_all [firstString, bind, Except.bind, pure, Except.pure]

def GetindexIntegerProperty : Prop :=
  (∀ (C : Type) (calls : ScalarIndexCalls C) error,
    calls.checkbounds = .error error → getindexInteger calls = .error error) ∧
  (∀ (C : Type) (calls : ScalarIndexCalls C) error,
    calls.checkbounds = .ok () → calls.isvalid = .error error →
    getindexInteger calls = .error error) ∧
  (∀ (C : Type) (calls : ScalarIndexCalls C),
    calls.checkbounds = .ok () → calls.isvalid = .ok false →
    getindexInteger calls = calls.stringIndexError) ∧
  (∀ (C : Type) (calls : ScalarIndexCalls C) character next,
    calls.checkbounds = .ok () → calls.isvalid = .ok true →
    calls.iterate = .ok (character, next) → getindexInteger calls = .ok character)

theorem getindexInteger_proven : GetindexIntegerProperty := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;>
    simp_all [getindexInteger, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

def GetindexVectorProperty : Prop :=
  (∀ (I C : Type) (v : IndexVectorInput I) getindex error,
    v.length = .error error →
    getindexVector v (getindex : I → SJl C) = .error error) ∧
  (∀ (I C : Type) (v : IndexVectorInput I) getindex size error,
    v.length = .ok size → v.values = .error error →
    getindexVector v (getindex : I → SJl C) = .error error) ∧
  (∀ (I C : Type) (v : IndexVectorInput I) getindex size indices,
    v.length = .ok size → v.values = .ok indices →
    getindexVector v (getindex : I → SJl C) = collectIndices getindex indices)

theorem getindexVector_proven : GetindexVectorProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [getindexVector, bind, Except.bind, pure, Except.pure]

def GetProperty : Prop :=
  (∀ (A : Type) (calls : GetCalls A) default error,
    calls.checkbounds = .error error → getDefault calls default = .error error) ∧
  (∀ (A : Type) (calls : GetCalls A) default,
    calls.checkbounds = .ok false → getDefault calls default = .ok default) ∧
  (∀ (A : Type) (calls : GetCalls A) default,
    calls.checkbounds = .ok true → getDefault calls default = calls.getindex)

theorem get_proven : GetProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [getDefault, bind, Except.bind, pure, Except.pure]

def CheckboundsIndexProperty : Prop :=
  (∀ (S I : Type) (s : AbstractStringInput S) (i : BoundsIndex I),
    i.oneLe = .ok false → checkboundsIndex s i = .ok false) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (i : BoundsIndex I) count,
    i.oneLe = .ok true → s.ncodeunits = .ok count →
    checkboundsIndex s i = i.leCodeunits count) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (i : BoundsIndex I) error,
    i.oneLe = .error error → checkboundsIndex s i = .error error)

theorem checkboundsIndex_proven : CheckboundsIndexProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [checkboundsIndex, bind, Except.bind, pure, Except.pure]

def CheckboundsRangeProperty : Prop :=
  (∀ (S I : Type) (s : AbstractStringInput S) (r : BoundsRange I),
    r.isempty = .ok true → checkboundsRange s r = .ok true) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (r : BoundsRange I) lo,
    r.isempty = .ok false → r.minimum = .ok lo → lo.oneLe = .ok false →
    checkboundsRange s r = .ok false) ∧
  (∀ (S I : Type) (s : AbstractStringInput S) (r : BoundsRange I) lo hi count,
    r.isempty = .ok false → r.minimum = .ok lo → lo.oneLe = .ok true →
    r.maximum = .ok hi → s.ncodeunits = .ok count →
    checkboundsRange s r = hi.leCodeunits count)

theorem checkboundsRange_proven : CheckboundsRangeProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [checkboundsRange, bind, Except.bind, pure, Except.pure]

def CheckboundsArrayProperty : Prop :=
  (∀ (I : Type) values check error,
    values = .error error →
    checkboundsArray values (check : I → SJl Bool) = .error error) ∧
  (∀ (I : Type) values check indices,
    values = .ok indices →
    checkboundsArray values (check : I → SJl Bool) = checkboundsArrayLoop check indices)

theorem checkboundsArray_proven : CheckboundsArrayProperty := by
  constructor <;> intros <;>
    simp_all [checkboundsArray, bind, Except.bind, pure, Except.pure]

def CheckboundsThrowProperty : Prop :=
  (∀ (S I : Type) (s : S) (indices : I),
    checkboundsThrow s indices (.ok true) = .ok ()) ∧
  (∀ (S I : Type) (s : S) (indices : I),
    checkboundsThrow s indices (.ok false) = .error (.jl .boundsError)) ∧
  (∀ (S I : Type) (s : S) (indices : I) error,
    checkboundsThrow s indices (.error error) = .error error)

theorem checkboundsThrow_proven : CheckboundsThrowProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> rfl

def VectorUInt8Property : Prop :=
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap error,
    s.string = .error error →
    vectorUInt8 s unsafeWrap = .error error) ∧
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap concrete,
    s.string = .ok concrete →
    vectorUInt8 s unsafeWrap = unsafeWrap concrete)

theorem vectorUInt8_proven : VectorUInt8Property := by
  constructor <;> intros <;>
    simp_all [vectorUInt8, bind, Except.bind, pure, Except.pure]

def ArrayUInt8Property : Prop :=
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap error,
    s.string = .error error →
    arrayUInt8 s unsafeWrap = .error error) ∧
  (∀ (S : Type) (s : ByteConversionInput S) unsafeWrap concrete,
    s.string = .ok concrete →
    arrayUInt8 s unsafeWrap = unsafeWrap concrete)

theorem arrayUInt8_proven : ArrayUInt8Property := by
  constructor <;> intros <;>
    simp_all [arrayUInt8, bind, Except.bind, pure, Except.pure]

def VectorAbstractCharProperty : Prop := ∀ (S C : Type) (s : S) collect,
  vectorAbstractChar s (collect : S → SJl (List C)) = collect s

theorem vectorAbstractChar_proven : VectorAbstractCharProperty := by
  unfold VectorAbstractCharProperty
  intros
  rfl

def SymbolAbstractStringProperty : Prop :=
  (∀ (S Sym : Type) (s : SymbolStringInput S Sym) error,
    s.string = .error error → symbolAbstractString s = .error error) ∧
  (∀ (S Sym : Type) (s : SymbolStringInput S Sym) concrete,
    s.string = .ok concrete → symbolAbstractString s = s.intern concrete)

theorem symbolAbstractString_proven : SymbolAbstractStringProperty := by
  constructor <;> intros <;>
    simp_all [symbolAbstractString, bind, Except.bind, pure, Except.pure]

def SymbolArgsProperty : Prop :=
  (∀ (Args Sym : Type) (args : SymbolArgsInput Args Sym) error,
    args.render args.values = .error error → symbolArgs args = .error error) ∧
  (∀ (Args Sym : Type) (args : SymbolArgsInput Args Sym) rendered,
    args.render args.values = .ok rendered → symbolArgs args = args.intern rendered)

theorem symbolArgs_proven : SymbolArgsProperty := by
  constructor <;> intros <;>
    simp_all [symbolArgs, bind, Except.bind, pure, Except.pure]

def ConvertProperty : Prop :=
  (∀ (S T : Type) (input : ConvertInput S T) error,
    input.construct input.value = .error error →
    convertAbstractString input = .error error) ∧
  (∀ (S T : Type) (input : ConvertInput S T) converted,
    input.construct input.value = .ok converted →
    convertAbstractString input = input.typeAssert converted)

theorem convert_proven : ConvertProperty := by
  constructor <;> intros <;>
    simp_all [convertAbstractString, bind, Except.bind, pure, Except.pure]

def SummaryProperty : Prop :=
  (∀ (S : Type) (input : SummaryInput S),
    input.isempty = .ok true →
    summary input = input.print ["empty", " ", input.typeName]) ∧
  (∀ (S : Type) (input : SummaryInput S) count,
    input.isempty = .ok false → input.ncodeunits = .ok count →
    summary input = input.print [toString count ++ "-codeunit", " ", input.typeName]) ∧
  (∀ (S : Type) (input : SummaryInput S) error,
    input.isempty = .error error → summary input = .error error)

theorem summary_proven : SummaryProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [summary, bind, Except.bind, pure, Except.pure]

def ConcatProperty : Prop :=
  (∀ (A R : Type) (input : ConcatInput A R),
    input.firstAnnotated = .ok true →
    concat input = input.annotatedstring input.first input.rest) ∧
  (∀ (A R : Type) (input : ConcatInput A R),
    input.firstAnnotated = .ok false → anyAnnotated input.restAnnotated = .ok true →
    concat input = input.annotatedstring input.first input.rest) ∧
  (∀ (A R : Type) (input : ConcatInput A R),
    input.firstAnnotated = .ok false → anyAnnotated input.restAnnotated = .ok false →
    concat input = input.string input.first input.rest)

theorem concat_proven : ConcatProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [concat, bind, Except.bind, pure, Except.pure]

def OneProperty : Prop := ∀ (T : Type) (converted : SJl T), oneString converted = converted
theorem one_proven : OneProperty := by
  unfold OneProperty
  intros
  rfl

def IsannotatedTypeProperty : Prop := ∀ kind,
  isannotatedType kind =
    match kind with
    | .bottom => false
    | .annotatedString => true
    | .annotatedChar => true
    | .other => false

theorem isannotatedType_proven : IsannotatedTypeProperty := by
  intro kind
  cases kind <;> rfl

def IsannotatedValueProperty : Prop := ∀ (V : Type) (input : ValueTypeInput V),
  isannotatedValue input = true ↔
    input.typeOf input.value = .annotatedString ∨
    input.typeOf input.value = .annotatedChar

theorem isannotatedValue_proven : IsannotatedValueProperty := by
  intro V input
  cases h : input.typeOf input.value <;> simp [isannotatedValue, isannotatedType, h]

theorem cmpCharacters_eq_zero [DecidableEq A] (lt : A → A → Bool) : ∀ a b,
    cmpCharacters lt a b = 0 ↔ a = b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [cmpCharacters]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [cmpCharacters]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simp [cmpCharacters, ih]
          · simp [cmpCharacters, h]
            split <;> omega

def CmpStringProperty : Prop := ∀ (A : Type) (_ : DecidableEq A) lt
    (a b : AbstractStringSequence A),
  cmpString lt a b = 0 ↔
    a.identity = b.identity ∨ a.characters = b.characters

theorem cmpString_proven : CmpStringProperty := by
  intro A inst lt a b
  by_cases hid : a.identity = b.identity
  · simp [cmpString, hid]
  · simp [cmpString, hid, cmpCharacters_eq_zero]

def EqStringProperty : Prop := ∀ (A : Type) (_ : DecidableEq A) lt
    (a b : AbstractStringSequence A),
  eqString lt a b = true ↔ a.identity = b.identity ∨ a.characters = b.characters

theorem eqString_proven : EqStringProperty := by
  intro A inst lt a b
  simpa only [eqString, beq_iff_eq] using cmpString_proven A inst lt a b

def IslessStringProperty : Prop := ∀ (A : Type) (_ : DecidableEq A) lt
    (a b : AbstractStringSequence A),
  islessString lt a b =
    if a.identity = b.identity then false
    else decide (cmpCharacters lt a.characters b.characters < 0)

theorem islessString_proven : IslessStringProperty := by
  intro A inst lt a b
  by_cases hid : a.identity = b.identity
  · simp [islessString, cmpString, hid]
  · simp [islessString, cmpString, hid]

def CmpSymbolProperty : Prop := ∀ a b,
  cmpSymbol a b = 0 ↔ a = b

theorem cmpSymbol_proven : CmpSymbolProperty := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [cmpSymbol, lexBytes]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [cmpSymbol, lexBytes]
      | cons y ys =>
          by_cases h : x = y
          · subst y
            simpa [cmpSymbol, lexBytes] using ih ys
          · simp [cmpSymbol, lexBytes, h]
            split <;> omega

def IslessSymbolProperty : Prop := ∀ a b,
  islessSymbol a b = decide (lexBytes a b < 0)

theorem islessSymbol_proven : IslessSymbolProperty := by
  intro a b
  unfold islessSymbol cmpSymbol
  cases h : lexBytes a b <;> simp

def LengthStringProperty : Prop :=
  (∀ (S : Type) (s : IndexStringInput S) lengthBetween error,
    s.ncodeunits = .error error →
    lengthString s lengthBetween = .error error) ∧
  (∀ (S : Type) (s : IndexStringInput S) lengthBetween last,
    s.ncodeunits = .ok last →
    lengthString s lengthBetween = lengthBetween s.value (ix 1) last)

theorem lengthString_proven : LengthStringProperty := by
  constructor <;> intros <;>
    simp_all [lengthString, bind, Except.bind, pure, Except.pure]

def LengthBetweenProperty : Prop :=
  (∀ (S : Type) (input : LengthBetweenInput S) firstCount,
    input.firstCodeunits = .ok firstCount →
    ¬(ix 0 < input.first && input.first ≤ firstCount + ix 1) →
    lengthBetween input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : LengthBetweenInput S) firstCount lastCount,
    input.firstCodeunits = .ok firstCount →
    ix 0 < input.first && input.first ≤ firstCount + ix 1 →
    input.lastCodeunits = .ok lastCount →
    ix 0 ≤ input.last && input.last < lastCount + ix 1 →
    lengthBetween input =
      countValid (input.isvalid input.string) (indexRange input.first input.last))

theorem lengthBetween_proven : LengthBetweenProperty := by
  constructor <;> intros <;>
    simp_all [lengthBetween, bind, Except.bind, pure, Except.pure]

def LengthIntegerProperty : Prop :=
  (∀ (S I J : Type) (s : S) (first : MachineIntegerInput I)
      (last : MachineIntegerInput J) lengthInt error,
    first.toInt = .error error →
    lengthInteger s first last lengthInt = .error error) ∧
  (∀ (S I J : Type) (s : S) (first : MachineIntegerInput I)
      (last : MachineIntegerInput J) lengthInt i error,
    first.toInt = .ok i → last.toInt = .error error →
    lengthInteger s first last lengthInt = .error error) ∧
  (∀ (S I J : Type) (s : S) (first : MachineIntegerInput I)
      (last : MachineIntegerInput J) lengthInt i j,
    first.toInt = .ok i → last.toInt = .ok j →
    lengthInteger s first last lengthInt = lengthInt s i j)

theorem lengthInteger_proven : LengthIntegerProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [lengthInteger, bind, Except.bind, pure, Except.pure]

def ThisindIntegerProperty : Prop :=
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) thisindInt error,
    index.toInt = .error error →
    thisindInteger s index thisindInt = .error error) ∧
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) thisindInt converted,
    index.toInt = .ok converted →
    thisindInteger s index thisindInt = thisindInt s converted)

theorem thisindInteger_proven : ThisindIntegerProperty := by
  constructor <;> intros <;>
    simp_all [thisindInteger, bind, Except.bind, pure, Except.pure]

def ThisindIntProperty : Prop :=
  (∀ (S : Type) (input : ThisindInput S) count,
    input.ncodeunits = .ok count → input.index.val = (count + ix 1).val →
    thisindInt input = .ok input.index) ∧
  (∀ (S : Type) (input : ThisindInput S) count,
    input.ncodeunits = .ok count → input.index.val ≠ (count + ix 1).val →
    ¬(ix 0 ≤ input.index ∧ input.index ≤ count + ix 1) →
    thisindInt input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : ThisindInput S) count,
    input.ncodeunits = .ok count → input.index.val ≠ (count + ix 1).val →
    ix 0 ≤ input.index ∧ input.index ≤ count + ix 1 →
    thisindInt input =
      thisindRewind (input.isvalid input.string) input.index.val.toNat input.index)

theorem thisindInt_proven : ThisindIntProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros
    simp_all [thisindInt, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [thisindInt, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [thisindInt, bind, Except.bind, pure, Except.pure]

def PrevindWrappersProperty : Prop :=
  (∀ (S I N : Type) (s : S) (index : MachineIntegerInput I)
      (count : MachineIntegerInput N) dispatch i n,
    index.toInt = .ok i → count.toInt = .ok n →
    previndIntegerN s index count dispatch = dispatch s i n) ∧
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) dispatch i,
    index.toInt = .ok i →
    previndIntegerOne s index dispatch = dispatch s i) ∧
  (∀ (S : Type) (s : S) index dispatch,
    previndOne s index dispatch = dispatch s index (ix 1))

theorem previndWrappers_proven : PrevindWrappersProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [previndIntegerN, previndIntegerOne, previndOne, bind, Except.bind,
      pure, Except.pure]

def PrevindIntNProperty : Prop :=
  (∀ (S : Type) (input : PrevindInput S), input.count < ix 0 →
    previndIntN input = .error (.jl (.argumentError "n cannot be negative"))) ∧
  (∀ (S : Type) (input : PrevindInput S) codeunits,
    ¬(input.count < ix 0) → input.ncodeunits = .ok codeunits →
    ¬(ix 0 < input.index ∧ input.index ≤ codeunits + ix 1) →
    previndIntN input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : PrevindInput S) codeunits,
    ¬(input.count < ix 0) → input.ncodeunits = .ok codeunits →
    ix 0 < input.index ∧ input.index ≤ codeunits + ix 1 → input.count.val ≠ 0 →
    previndIntN input =
      previndLoop (input.isvalid input.string) input.index.val.toNat input.index input.count)

theorem previndIntN_proven : PrevindIntNProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros; simp_all [previndIntN]
  · intros
    simp_all [previndIntN, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [previndIntN, bind, Except.bind, pure, Except.pure]

def NextindWrappersProperty : Prop :=
  (∀ (S I N : Type) (s : S) (index : MachineIntegerInput I)
      (count : MachineIntegerInput N) dispatch i n,
    index.toInt = .ok i → count.toInt = .ok n →
    nextindIntegerN s index count dispatch = dispatch s i n) ∧
  (∀ (S I : Type) (s : S) (index : MachineIntegerInput I) dispatch i,
    index.toInt = .ok i →
    nextindIntegerOne s index dispatch = dispatch s i (ix 1)) ∧
  (∀ (S : Type) (s : S) index dispatch,
    nextindOne s index dispatch = dispatch s index (ix 1))

theorem nextindWrappers_proven : NextindWrappersProperty := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;>
    simp_all [nextindIntegerN, nextindIntegerOne, nextindOne, bind, Except.bind,
      pure, Except.pure]

def NextindIntNProperty : Prop :=
  (∀ (S : Type) (input : NextindInput S), input.count < ix 0 →
    nextindIntN input = .error (.jl (.argumentError "n cannot be negative"))) ∧
  (∀ (S : Type) (input : NextindInput S) last,
    ¬(input.count < ix 0) → input.ncodeunits = .ok last →
    ¬(ix 0 ≤ input.index ∧ input.index ≤ last) →
    nextindIntN input = .error (.jl .boundsError)) ∧
  (∀ (S : Type) (input : NextindInput S) last,
    ¬(input.count < ix 0) → input.ncodeunits = .ok last →
    ix 0 ≤ input.index ∧ input.index ≤ last → input.count.val ≠ 0 →
    nextindIntN input = nextindLoop (input.isvalid input.string) last
      (last.val - input.index.val).toNat input.index input.count)

theorem nextindIntN_proven : NextindIntNProperty := by
  refine ⟨?_, ?_, ?_⟩
  · intros; simp_all [nextindIntN]
  · intros
    simp_all [nextindIntN, bind, Except.bind, pure, Except.pure]
  · intros
    simp_all [nextindIntN, bind, Except.bind, pure, Except.pure]
def KeysProperty : Prop := ∀ (S : Type) (s : S), (keys s).string = s
theorem keys_proven : KeysProperty := by unfold KeysProperty; intros; rfl
def EachLengthProperty : Prop := ∀ (S : Type) (index : EachStringIndex S) length,
  eachLength index length = length index.string
theorem eachLength_proven : EachLengthProperty := by unfold EachLengthProperty; intros; rfl
def EachLastProperty : Prop := ∀ (S : Type) (index : EachStringIndex S) lastindex,
  eachLast index lastindex = lastindex index.string
theorem eachLast_proven : EachLastProperty := by unfold EachLastProperty; intros; rfl

def EachIterateProperty : Prop :=
  (∀ (S : Type) (input : EachIterateInput S) state last,
    input.state = some state → input.ncodeunits input.index.string = .ok last →
    last < state → eachIterate input = .ok none) ∧
  (∀ (S : Type) (input : EachIterateInput S) state last,
    input.state = some state → input.ncodeunits input.index.string = .ok last →
    ¬(last < state) → eachIterate input = do
      let next ← input.nextind input.index.string state
      return some (state, next))

theorem eachIterate_proven : EachIterateProperty := by
  constructor <;> intros <;>
    simp_all [eachIterate, bind, Except.bind, pure, Except.pure]

def IsasciiStringProperty : Prop :=
  (∀ (C : Type) (input : AsciiStringInput C) error,
    input.characters = .error error → isasciiString input = .error error) ∧
  (∀ (C : Type) (input : AsciiStringInput C) characters,
    input.characters = .ok characters →
    isasciiString input = allAscii input.isascii characters)

theorem isasciiString_proven : IsasciiStringProperty := by
  constructor <;> intros <;>
    simp_all [isasciiString, bind, Except.bind, pure, Except.pure]

def IsasciiAbstractCharProperty : Prop :=
  (∀ value, isasciiAbstractChar (.ok value) = .ok (value < 0x80)) ∧
  (∀ error, isasciiAbstractChar (.error error) = .error error)

theorem isasciiAbstractChar_proven : IsasciiAbstractCharProperty := by
  constructor <;> intros <;> rfl

def IsasciiRangeProperty : Prop := ∀ (CU V : Type) (ops : CodeUnitOps CU V) first last aggregate,
  isasciiRangeLoop ops last (last.val - first.val + 1).toNat first ops.zero = .ok aggregate →
  isasciiRange ops first last = .ok (ops.nonnegative aggregate && ops.below80 aggregate)

theorem isasciiRange_proven : IsasciiRangeProperty := by
  unfold IsasciiRangeProperty
  intros
  simp_all [isasciiRange, bind, Except.bind, pure, Except.pure]

def IsasciiChunksProperty : Prop := ∀ range chunkSize first last,
  isasciiChunks range chunkSize first last =
    isasciiChunksLoop range chunkSize last
      ((last.val - first.val + 1).toNat + 1) first

theorem isasciiChunks_proven : IsasciiChunksProperty := by
  unfold IsasciiChunksProperty
  intros
  rfl

def IsasciiVectorProperty : Prop :=
  (∀ input first last,
    input.firstindex = .ok first → input.lastindex = .ok last →
    last - first + ix 1 < ix 1536 →
    isasciiVector input = input.range first last) ∧
  (∀ input first last,
    input.firstindex = .ok first → input.lastindex = .ok last →
    ¬(last - first + ix 1 < ix 1536) →
    isasciiVector input = input.chunks (ix 1024) first last)

theorem isasciiVector_proven : IsasciiVectorProperty := by
  constructor <;> intros <;>
    simp_all [isasciiVector, bind, Except.bind, pure, Except.pure]

def MapProperty : Prop :=
  (∀ (S C M B : Type) (input : MapInput S C M B) error,
    input.sizeof = .error error → mapString input = .error error) ∧
  (∀ (S C M B : Type) (input : MapInput S C M B) bytes unitSize capacity buffer characters,
    input.sizeof = .ok bytes → input.codeunitSize = .ok unitSize →
    divStringInt bytes unitSize = .ok capacity →
    input.allocate (if capacity < ix 4 then ix 4 else capacity) = .ok buffer →
    input.characters = .ok characters →
    mapString input = do
      let result ← mapLoop input characters buffer (ix 1)
      let resized ← input.resize result.1 (result.2 - ix 1)
      let hinted ← input.sizehint resized (result.2 - ix 1)
      input.makeString hinted)

theorem map_proven : MapProperty := by
  constructor <;> intros <;>
    simp_all [mapString, bind, Except.bind, pure, Except.pure]

def FilterProperty : Prop :=
  (∀ (S C B : Type) (input : FilterInput S C B) error,
    input.sizeof = .error error → filterString input = .error error) ∧
  (∀ (S C B : Type) (input : FilterInput S C B) size buffer characters,
    input.sizeof = .ok size → input.makeBuffer size = .ok buffer →
    input.characters = .ok characters →
    filterString input = do
      let result ← filterLoop input characters buffer
      input.takestring result)

theorem filter_proven : FilterProperty := by
  constructor <;> intros <;>
    simp_all [filterString, bind, Except.bind, pure, Except.pure]

def FirstNProperty : Prop := ∀ (S I R : Type) (input : FirstNInput S I R) advanced last,
  input.nextind input.string (ix 0) input.count = .ok advanced →
  input.lastindex input.string = .ok last →
  firstN input = input.slice input.string (ix 1) (if advanced < last then advanced else last)

theorem firstN_proven : FirstNProperty := by
  unfold FirstNProperty
  intros
  simp_all [firstN, bind, Except.bind, pure, Except.pure]

def LastNProperty : Prop := ∀ (S I R : Type) (input : LastNInput S I R) count first,
  input.ncodeunits input.string = .ok count →
  input.prevind input.string (count + ix 1) input.count = .ok first →
  lastN input = input.slice input.string (if first < ix 1 then ix 1 else first)

theorem lastN_proven : LastNProperty := by
  unfold LastNProperty
  intros
  simp_all [lastN, bind, Except.bind, pure, Except.pure]

def ReverseindProperty : Prop := ∀ (I : Type) ncodeunits (index : MachineIntegerInput I)
    thisind count converted,
  ncodeunits = .ok count → index.toInt = .ok converted →
  reverseind ncodeunits index thisind = thisind (count - converted + ix 1)

theorem reverseind_proven : ReverseindProperty := by
  unfold ReverseindProperty
  intros
  simp_all [reverseind, bind, Except.bind, pure, Except.pure]

def RepeatProperty : Prop := ∀ (I : Type) string count repeatFn concrete,
  string = .ok concrete →
  repeatString string (count : I) repeatFn = repeatFn concrete count

theorem repeat_proven : RepeatProperty := by
  unfold RepeatProperty
  intros
  simp_all [repeatString, bind, Except.bind, pure, Except.pure]

def PowerProperty : Prop := ∀ (A I R : Type) value count repeatFn,
  powerString value count (repeatFn : A → I → SJl R) = repeatFn value count

theorem power_proven : PowerProperty := by unfold PowerProperty; intros; rfl

def ReverseIterateProperty : Prop :=
  (∀ (S A : Type) (input : ReverseIterateInput S A) state first,
    input.state = some state → input.firstindex input.string = .ok first →
    state < first → reverseIterate input = .ok none) ∧
  (∀ (S A : Type) (input : ReverseIterateInput S A) state first,
    input.state = some state → input.firstindex input.string = .ok first →
    ¬(state < first) → reverseIterate input = do
      let value ← input.getindex input.string state
      let previous ← input.prevind input.string state
      return some (value, previous))

theorem reverseIterate_proven : ReverseIterateProperty := by
  constructor <;> intros <;>
    simp_all [reverseIterate, bind, Except.bind, pure, Except.pure]
def CodeUnitsCtorProperty : Prop := ∀ (S T : Type) (s : S),
  (codeUnitsCtor (T := T) s).string = s
theorem codeUnitsCtor_proven : CodeUnitsCtorProperty := by
  unfold CodeUnitsCtorProperty
  intros
  rfl

def CuSizeofProperty : Prop := ∀ (S T : Type) (s : CodeUnits S T) ncodeunits sizeofType count unitSize,
  ncodeunits s.string = .ok count → sizeofType = .ok unitSize →
  cuSizeof s ncodeunits sizeofType = .ok (count * unitSize)
theorem cuSizeof_proven : CuSizeofProperty := by
  unfold CuSizeofProperty
  intros
  simp_all [cuSizeof, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
def CuSizeProperty : Prop := ∀ (S T : Type) (s : CodeUnits S T) ncodeunits count,
  ncodeunits s.string = .ok count → cuSize s ncodeunits = .ok (count, ())
theorem cuSize_proven : CuSizeProperty := by
  unfold CuSizeProperty
  intros
  simp_all [cuSize, bind, Except.bind, pure, Except.pure]
def CuElsizeProperty : Prop := ∀ sizeofType : SJl JInt64, cuElsize sizeofType = sizeofType
theorem cuElsize_proven : CuElsizeProperty := by unfold CuElsizeProperty; intros; rfl
def CuGetindexProperty : Prop := ∀ (S T : Type) (s : CodeUnits S T) index codeunit,
  cuGetindex s index codeunit = codeunit s.string index
theorem cuGetindex_proven : CuGetindexProperty := by unfold CuGetindexProperty; intros; rfl
def CuCheckboundsProperty : Prop := ∀ (S T I : Type) (s : CodeUnits S T)
    (index : I) (checkbounds : S → I → SJl Bool),
  cuCheckbounds s index checkbounds = checkbounds s.string index
theorem cuCheckbounds_proven : CuCheckboundsProperty := by unfold CuCheckboundsProperty; intros; rfl
def CuDataidsProperty : Prop := ∀ (S T R : Type) (s : CodeUnits S T) dataids,
  cuDataids s (dataids : S → SJl R) = dataids s.string
theorem cuDataids_proven : CuDataidsProperty := by unfold CuDataidsProperty; intros; rfl
def CuWriteProperty : Prop := ∀ (IOType S T R : Type) io (s : CodeUnits S T) write,
  cuWrite io s (write : IOType → S → SJl R) = write io s.string
theorem cuWrite_proven : CuWriteProperty := by unfold CuWriteProperty; intros; rfl
def CuCconvertProperty : Prop := ∀ (S T P : Type) target (s : CodeUnits S T) cconvert,
  cuCconvert target s (cconvert : PointerTarget T → S → SJl P) = cconvert target s.string
theorem cuCconvert_proven : CuCconvertProperty := by unfold CuCconvertProperty; intros; rfl
def CuSimilarProperty : Prop := ∀ (Dims A : Type) dims similarArray,
  cuSimilar dims (similarArray : Dims → SJl A) = similarArray dims
theorem cuSimilar_proven : CuSimilarProperty := by unfold CuSimilarProperty; intros; rfl
def CodeunitsProperty : Prop := ∀ (S T : Type) (s : S),
  (codeunits (T := T) s).string = s
theorem codeunits_proven : CodeunitsProperty := by unfold CodeunitsProperty; intros; rfl

def SplitRestProperty : Prop :=
  (∀ (S R : Type) (input : SplitRestInput S R) last split,
    input.lastindex input.string = .ok last →
    input.prevind input.string last input.count = .ok split →
    splitRest input = do
      let suffixStart ← input.nextind input.string split
      let suffix ← input.substring input.string suffixStart last
      let frontResult ← input.front input.string split
      return (frontResult, suffix)) ∧
  (∀ (S R : Type) (input : SplitRestInput S R) last length,
    input.lastindex input.string = .ok last →
    input.prevind input.string last input.count = .error (.jl .boundsError) →
    input.length input.string = .ok length →
    splitRest input = do
      let split ← input.checkLength length input.count
      let suffixStart ← input.nextind input.string split
      let suffix ← input.substring input.string suffixStart last
      let frontResult ← input.front input.string split
      return (frontResult, suffix))

theorem splitRest_proven : SplitRestProperty := by
  constructor <;> intros <;>
    simp_all [splitRest, bind, Except.bind, pure, Except.pure]

end JuliaLean.StringsCovA.BasicRebuilt
